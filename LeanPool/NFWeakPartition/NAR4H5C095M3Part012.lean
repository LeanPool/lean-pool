/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part011

/-! NF weak partition development: NAR4H5C095M3Part012. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0008`. -/
@[expose]
noncomputable def nb095SplitAlpha0008 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy175 D R S_cls E))
          (Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy175 D R S_cls E))
            (Class.cab (nb095AlphaDummy169 D R S_cls E)
              (synWrex (nb095AlphaDummy170 D R S_cls E)
                (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy176 f))
          (Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy176 f))
            (Class.cab (nb095AlphaDummy171 f)
              (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                  (synCphi (Class.cv (nb095AlphaDummy172 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                      (nb095AlphaDummy170 D R S_cls E) from (by
                      unfold nb095AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
                  (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy172 f) from (by
                      unfold nb095AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                        (nb095AlphaDummy169 D R S_cls E) from (by
                        unfold nb095AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 0))))
                    (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy171 f) from (by
                        unfold nb095AlphaDummy171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0174 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy013 D R S_cls E) ≠
                          (nb095AlphaDummy175 D R S_cls E) from (by
                          unfold nb095AlphaDummy175;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0176 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy176 f) from (by
                          unfold nb095AlphaDummy176;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0177 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                            (nb095AlphaDummy173 D R S_cls E) from (by
                            unfold nb095AlphaDummy173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0173 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy174 f) from (by
                            unfold nb095AlphaDummy174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0175 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                              (nb095AlphaDummy177 D R S_cls E) from (by
                              unfold nb095AlphaDummy177;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      0))))
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
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from (by
                                unfold nb095AlphaDummy180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy172 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls
                    E)
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
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy181 D R S_cls E) from (by
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
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
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
                    D R S_cls
                    E)
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
                    S_cls E)
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls
                    E)
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
                    S_cls E)
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
                    D R S_cls
                    E)
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
                    S_cls E)
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls
                    E)
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
                    S_cls E)
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
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
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
                    D R S_cls
                    E)
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
                    S_cls E)
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls
                    E)
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
                    S_cls E)
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls
                    E)
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
                    S_cls E)
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
                    D R S_cls
                    E)
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
                    S_cls E)
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
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy181 D R S_cls E),
                                      (nb095AlphaDummy182 f)),
                                    ((nb095AlphaDummy177 D R S_cls E),
                                      (nb095AlphaDummy179 f)),
                                    ((nb095AlphaDummy178 D R S_cls E),
                                      (nb095AlphaDummy180 f)),
                                    ((nb095AlphaDummy170 D R S_cls E),
                                      (nb095AlphaDummy172 f)),
                                    ((nb095AlphaDummy169 D R S_cls E),
                                      (nb095AlphaDummy171 f)),
                                    ((nb095AlphaDummy175 D R S_cls E),
                                      (nb095AlphaDummy176 f)),
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
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
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
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy181 D R S_cls E),
                                      (nb095AlphaDummy182 f)),
                                    ((nb095AlphaDummy177 D R S_cls E),
                                      (nb095AlphaDummy179 f)),
                                    ((nb095AlphaDummy178 D R S_cls E),
                                      (nb095AlphaDummy180 f)),
                                    ((nb095AlphaDummy170 D R S_cls E),
                                      (nb095AlphaDummy172 f)),
                                    ((nb095AlphaDummy169 D R S_cls E),
                                      (nb095AlphaDummy171 f)),
                                    ((nb095AlphaDummy175 D R S_cls E),
                                      (nb095AlphaDummy176 f)),
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
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                        (nb095AlphaDummy170 D R S_cls E) from (by
                        unfold nb095AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
                    (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy172 f) from (by
                        unfold nb095AlphaDummy172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0174 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy013 D R S_cls E) ≠
                          (nb095AlphaDummy169 D R S_cls E) from (by
                          unfold nb095AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy171 f) from (by
                          unfold nb095AlphaDummy171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0174 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                            (nb095AlphaDummy175 D R S_cls E) from (by
                            unfold nb095AlphaDummy175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0176 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy176 f) from (by
                            unfold nb095AlphaDummy176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0177 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                              (nb095AlphaDummy173 D R S_cls E) from (by
                              unfold nb095AlphaDummy173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0173 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy174 f) from (by
                              unfold nb095AlphaDummy174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0175 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
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
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
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
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
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
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy175 D R S_cls E),
                                        (nb095AlphaDummy176 f)),
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
                                      ((nb095AlphaDummy009 D R S_cls E),
                                        (nb095AlphaDummy010 f)),
                                      ((nb095AlphaDummy007 D R S_cls E),
                                        (nb095AlphaDummy008 f)),
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
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy175 D R S_cls E),
                                        (nb095AlphaDummy176 f)),
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
                                      ((nb095AlphaDummy009 D R S_cls E),
                                        (nb095AlphaDummy010 f)),
                                      ((nb095AlphaDummy007 D R S_cls E),
                                        (nb095AlphaDummy008 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0009`. -/
@[expose]
noncomputable def nb095SplitAlpha0009 (x : Var) (u : Var) (D : Class) (R : Class)
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
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095AlphaDummy201 D R S_cls E))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy202 f))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy172 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                            (nb095AlphaDummy177 D R S_cls E) from (by
                            unfold nb095AlphaDummy177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                    0))))
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
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from (by
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
                                        (nb095_support_mem_0208 D R S_cls E) 0))))
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy204 f) from (by
                                unfold nb095AlphaDummy204;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0209 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                  (nb095AlphaDummy201 D R S_cls E) from (by
                                  unfold nb095AlphaDummy201;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0206 D R S_cls E) 0))))
                              (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy202 f) from
                                (by
                                  unfold nb095AlphaDummy202;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy172 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls E)
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
                  (nb095_support_mem_0182 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy186 f) from (by
          unfold nb095AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy181 D R S_cls E) from (by
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
                  (nb095_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
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
                    D R S_cls
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
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
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
                    D R S_cls
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
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy184 D
        R S_cls E) ≠ (nb095AlphaDummy195 D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185 D
        R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
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
                    D R S_cls
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185 D
        R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
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
                    D R S_cls
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
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                    (by
                                      unfold nb095AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy181 D R S_cls E),
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
                                  ((nb095AlphaDummy009 D R S_cls E),
                                    (nb095AlphaDummy010 f)),
                                  ((nb095AlphaDummy007 D R S_cls E),
                                    (nb095AlphaDummy008 f)),
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
                                  (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from (by
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
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                    (by
                                      unfold nb095AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy181 D R S_cls E),
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
                                  ((nb095AlphaDummy009 D R S_cls E),
                                    (nb095AlphaDummy010 f)),
                                  ((nb095AlphaDummy007 D R S_cls E),
                                    (nb095AlphaDummy008 f)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                            (nb095AlphaDummy177 D R S_cls E) from (by
                            unfold nb095AlphaDummy177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                    0))))
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
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from (by
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
                                        (nb095_support_mem_0208 D R S_cls E) 0))))
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy204 f) from (by
                                unfold nb095AlphaDummy204;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0209 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                  (nb095AlphaDummy201 D R S_cls E) from (by
                                  unfold nb095AlphaDummy201;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0206 D R S_cls E) 0))))
                              (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy202 f) from
                                (by
                                  unfold nb095AlphaDummy202;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy172 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls E)
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
                  (nb095_support_mem_0182 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy186 f) from (by
          unfold nb095AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy181 D R S_cls E) from (by
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
                  (nb095_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
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
                    D R S_cls
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
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
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
                    D R S_cls
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
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy184 D
        R S_cls E) ≠ (nb095AlphaDummy195 D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
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
                    D R S_cls
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
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185 D
        R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
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
                    D R S_cls
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185 D
        R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
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
                    D R S_cls
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
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                    (by
                                      unfold nb095AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy181 D R S_cls E),
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
                                  ((nb095AlphaDummy009 D R S_cls E),
                                    (nb095AlphaDummy010 f)),
                                  ((nb095AlphaDummy007 D R S_cls E),
                                    (nb095AlphaDummy008 f)),
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
                                  (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from (by
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
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                    (by
                                      unfold nb095AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy181 D R S_cls E),
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
                                  ((nb095AlphaDummy009 D R S_cls E),
                                    (nb095AlphaDummy010 f)),
                                  ((nb095AlphaDummy007 D R S_cls E),
                                    (nb095AlphaDummy008 f)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0010`. -/
@[expose]
noncomputable def nb095SplitAlpha0010 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classEq (Class.cv (nb095AlphaDummy017 D R S_cls E))
          (synCop (Class.cv (nb095AlphaDummy011 D R S_cls E))
            (Class.cv (nb095AlphaDummy012 D R S_cls E)))) (Wff.neg
          (synWex (nb095AlphaDummy013 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy013 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy012 D R S_cls E)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb095AlphaDummy018 f))
          (synCop (Class.cv (nb095AlphaDummy014 f)) (Class.cv (nb095AlphaDummy015 f))))
        (Wff.neg (synWex (nb095AlphaDummy016 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy014 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy016 f)))
              (synWbr (Class.cv (nb095AlphaDummy016 f)) (Class.cv f)
                (Class.cv (nb095AlphaDummy015 f))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
              (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy017 D R S_cls E) from (by
                unfold nb095AlphaDummy017;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0002 D R S_cls E) 0))))) (Ne.symm
            (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy018 f) from (by
                unfold nb095AlphaDummy018;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0003 f) 0)))))
          (TAlphaVar.there (Ne.symm (show
                (nb095AlphaDummy011 D R S_cls E) ≠ (nb095AlphaDummy017 D R S_cls E) from
                (by
                  unfold nb095AlphaDummy017;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0000 D R S_cls E) 0))))) (Ne.symm
              (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy018 f) from (by
                  unfold nb095AlphaDummy018;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0001 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0000 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy012 D R S_cls E) ≠
                                      (nb095AlphaDummy020 D R S_cls E) from (by
                                      unfold nb095AlphaDummy020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0032 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy022 f) from
                                    (by
                                      unfold nb095AlphaDummy022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy012 D R S_cls E) ≠
                                        (nb095AlphaDummy019 D R S_cls E) from (by
                                        unfold nb095AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0032 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy021 f) from
                                      (by
                                        unfold nb095AlphaDummy021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy049 D R S_cls E) from (by
                                          unfold nb095AlphaDummy049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0036 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy015 f) ≠
        (nb095AlphaDummy050 f) from (by
                                          unfold nb095AlphaDummy050;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy023 D R S_cls E) from (by
          unfold nb095AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0033 D R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy024 f) from (by
          unfold nb095AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy014 f))).fv ∪
                                      ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg
                                    (nb095SplitAlpha0001 x u D R S_cls f E)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy012 D R S_cls E) ≠
                                      (nb095AlphaDummy020 D R S_cls E) from (by
                                      unfold nb095AlphaDummy020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0032 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy022 f) from
                                    (by
                                      unfold nb095AlphaDummy022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy012 D R S_cls E) ≠
                                        (nb095AlphaDummy019 D R S_cls E) from (by
                                        unfold nb095AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0032 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy021 f) from
                                      (by
                                        unfold nb095AlphaDummy021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy049 D R S_cls E) from (by
                                          unfold nb095AlphaDummy049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0036 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy015 f) ≠
        (nb095AlphaDummy050 f) from (by
                                          unfold nb095AlphaDummy050;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy023 D R S_cls E) from (by
          unfold nb095AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0033 D R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy024 f) from (by
          unfold nb095AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy014 f))).fv ∪
                                      ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb095SplitAlpha0001 x u D R S_cls f
                                      E))))))))))))))))) (TAlphaWff.neg (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg
                        (TAlphaWff.neg (nb095SplitAlpha0002 x u D R S_cls f E)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy056 D R S_cls E) from (by
          unfold nb095AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  1)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy058 f) from (by
          unfold nb095AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy055 D R S_cls E) from (by
          unfold nb095AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy057 f) from (by
          unfold nb095AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy085 D R S_cls E) from (by
          unfold nb095AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy086 f) from (by
          unfold nb095AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy059 D R S_cls E) from (by
          unfold nb095AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy060 f) from (by
          unfold nb095AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy011 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy013 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy016 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0003 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy087 D R S_cls E), (nb095AlphaDummy088 f)),
        ((nb095AlphaDummy056 D R S_cls E), (nb095AlphaDummy058 f)),
        ((nb095AlphaDummy055 D R S_cls E), (nb095AlphaDummy057 f)),
        ((nb095AlphaDummy085 D R S_cls E), (nb095AlphaDummy086 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy056 D R S_cls E) from (by
          unfold nb095AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  1)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy058 f) from (by
          unfold nb095AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy055 D R S_cls E) from (by
          unfold nb095AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy057 f) from (by
          unfold nb095AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy085 D R S_cls E) from (by
          unfold nb095AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy086 f) from (by
          unfold nb095AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy059 D R S_cls E) from (by
          unfold nb095AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy060 f) from (by
          unfold nb095AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy011 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy013 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy016 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0003 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy087 D R S_cls E), (nb095AlphaDummy088 f)),
        ((nb095AlphaDummy056 D R S_cls E), (nb095AlphaDummy058 f)),
        ((nb095AlphaDummy055 D R S_cls E), (nb095AlphaDummy057 f)),
        ((nb095AlphaDummy085 D R S_cls E), (nb095AlphaDummy086 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb095AlphaDummy092 D R S_cls E) ≠
                                (nb095AlphaDummy095 D R S_cls E) from (by
                                unfold nb095AlphaDummy095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0082 D R S_cls E) 0))))) (Ne.symm
                            (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy096 f) from (by
                                unfold nb095AlphaDummy096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0083 f) 0)))))
                          (TAlphaVar.there (Ne.symm (show (nb095AlphaDummy091 D R S_cls E) ≠
                                  (nb095AlphaDummy095 D R S_cls E) from (by
                                  unfold nb095AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0080 D R S_cls E) 0))))) (Ne.symm
                              (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy096 f) from
                                (by
                                  unfold nb095AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0081 f) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0004 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0005 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129 D R S_cls
        E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E),
        (nb095AlphaDummy099 f)), ((nb095AlphaDummy127 D R S_cls E),
        (nb095AlphaDummy128 f)), ((nb095AlphaDummy101 D R S_cls E),
        (nb095AlphaDummy102 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy009 D R S_cls E),
        (nb095AlphaDummy010 f)), ((nb095AlphaDummy007 D R S_cls E),
        (nb095AlphaDummy008 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0005 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129 D R S_cls
        E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E),
        (nb095AlphaDummy099 f)), ((nb095AlphaDummy127 D R S_cls E),
        (nb095AlphaDummy128 f)), ((nb095AlphaDummy101 D R S_cls E),
        (nb095AlphaDummy102 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy009 D R S_cls E),
        (nb095AlphaDummy010 f)), ((nb095AlphaDummy007 D R S_cls E),
        (nb095AlphaDummy008 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0006 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0007 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy165 D R S_cls
        E), (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy009 D R S_cls E),
        (nb095AlphaDummy010 f)), ((nb095AlphaDummy007 D R S_cls E),
        (nb095AlphaDummy008 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0007 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy165 D R S_cls
        E), (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy009 D R S_cls E),
        (nb095AlphaDummy010 f)), ((nb095AlphaDummy007 D R S_cls E),
        (nb095AlphaDummy008 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy092 D R S_cls E) from (by
                              unfold nb095AlphaDummy092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                      1)))) (show f ≠ (nb095AlphaDummy094 f) from (by
                              unfold nb095AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy091 D R S_cls E) from (by
                                unfold nb095AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0170 D R S_cls E) 0))))
                            (show f ≠ (nb095AlphaDummy093 f) from (by
                                unfold nb095AlphaDummy093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0171 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy095 D R S_cls E) from (by
                                  unfold nb095AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0168 D R S_cls E) 0))))
                              (show f ≠ (nb095AlphaDummy096 f) from (by
                                  unfold nb095AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0169 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy013 D R S_cls E) from (by
                                    unfold nb095AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0164 D R S_cls E) 2))))
                                (show f ≠ (nb095AlphaDummy016 f) from (by
                                    unfold nb095AlphaDummy016;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0166 f)
                                            2)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy012 D R S_cls E) from (by
                                      unfold nb095AlphaDummy012;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0164 D R S_cls E) 1))))
                                  (show f ≠ (nb095AlphaDummy015 f) from (by
                                      unfold nb095AlphaDummy015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0166 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy011 D R S_cls E) from (by
                                        unfold nb095AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0164 D R S_cls E) 0))))
                                    (show f ≠ (nb095AlphaDummy014 f) from (by
                                        unfold nb095AlphaDummy014;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0166 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy017 D R S_cls E) from (by
                                          unfold nb095AlphaDummy017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0165 D R S_cls E)
                                                  0)))) (show f ≠ (nb095AlphaDummy018 f) from
                                        (by
                                          unfold nb095AlphaDummy018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0167 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy009 D R S_cls E) from (by
          unfold nb095AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0162 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy010 f) from (by
          unfold nb095AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy007 D R S_cls E) from (by
          unfold nb095AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0160 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy008 f) from (by
          unfold nb095AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0161 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg
                        (TAlphaWff.neg (nb095SplitAlpha0008 x u D R S_cls f E)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy170 D R S_cls E) from (by
          unfold nb095AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  1)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy172 f) from (by
          unfold nb095AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy169 D R S_cls E) from (by
          unfold nb095AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy171 f) from (by
          unfold nb095AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy199 D R S_cls E) from (by
          unfold nb095AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy200 f) from (by
          unfold nb095AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy173 D R S_cls E) from (by
          unfold nb095AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy174 f) from (by
          unfold nb095AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv (Class.cv
        (nb095AlphaDummy000 D R S_cls E)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy013 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy012 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy016 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0009 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy170 D R S_cls E) from (by
          unfold nb095AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  1)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy172 f) from (by
          unfold nb095AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy169 D R S_cls E) from (by
          unfold nb095AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy171 f) from (by
          unfold nb095AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy199 D R S_cls E) from (by
          unfold nb095AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy200 f) from (by
          unfold nb095AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy173 D R S_cls E) from (by
          unfold nb095AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy174 f) from (by
          unfold nb095AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv (Class.cv
        (nb095AlphaDummy000 D R S_cls E)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy013 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy012 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy016 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0009 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy201 D R S_cls E), (nb095AlphaDummy202 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy199 D R S_cls E), (nb095AlphaDummy200 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                  (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy013 D R S_cls E) from
                  (by
                    unfold nb095AlphaDummy013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 2))))
                (show f ≠ (nb095AlphaDummy016 f) from (by
                    unfold nb095AlphaDummy016;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0166 f) 2))))
                (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                      (nb095AlphaDummy012 D R S_cls E) from (by
                      unfold nb095AlphaDummy012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 1))))
                  (show f ≠ (nb095AlphaDummy015 f) from (by
                      unfold nb095AlphaDummy015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0166 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                        (nb095AlphaDummy011 D R S_cls E) from (by
                        unfold nb095AlphaDummy011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 0))))
                    (show f ≠ (nb095AlphaDummy014 f) from (by
                        unfold nb095AlphaDummy014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0166 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy000 D R S_cls E) ≠
                          (nb095AlphaDummy017 D R S_cls E) from (by
                          unfold nb095AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0165 D R S_cls E)
                                  0)))) (show f ≠ (nb095AlphaDummy018 f) from (by
                          unfold nb095AlphaDummy018;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0167 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                            (nb095AlphaDummy009 D R S_cls E) from (by
                            unfold nb095AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0162 D R S_cls E)
                                    0)))) (show f ≠ (nb095AlphaDummy010 f) from (by
                            unfold nb095AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0163 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy007 D R S_cls E) from (by
                              unfold nb095AlphaDummy007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0160 D R S_cls E)
                                      0)))) (show f ≠ (nb095AlphaDummy008 f) from (by
                              unfold nb095AlphaDummy008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0161 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                              (by decide)) dv_f_u (TAlphaVar.there
                              (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                                (by decide)) dv_f_x (TAlphaVar.here _ _ _)))))))))))))))

theorem nb095_wpp_notmem_0506 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy009 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy009, fv_syn_cid] using
    (nb095_compact_fv_empty_0026 D R S_cls E)

theorem nb095_wpp_notmem_0507 (f : Var) : (nb095AlphaDummy010 f) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy010, fv_syn_cid] using (nb095_compact_fv_empty_0027 f)

theorem nb095_wpp_notmem_0508 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy007 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy007, fv_syn_cid] using
    (nb095_compact_fv_empty_0028 D R S_cls E)

theorem nb095_wpp_notmem_0509 (f : Var) : (nb095AlphaDummy008 f) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy008, fv_syn_cid] using (nb095_compact_fv_empty_0029 f)

theorem nb095_wpp_notmem_0510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy001, fv_syn_cid] using
    (nb095_compact_fv_empty_0030 D R S_cls E)

theorem nb095_wpp_notmem_0511 (u : Var) : u ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb095_compact_fv_empty_0031 u)

theorem nb095_wpp_notmem_0512 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy002, fv_syn_cid] using
    (nb095_compact_fv_empty_0032 D R S_cls E)

theorem nb095_wpp_notmem_0513 (x : Var) : x ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb095_compact_fv_empty_0033 x)

theorem nb095_wpp_notmem_0514 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy000, fv_syn_cid] using
    (nb095_compact_fv_empty_0034 D R S_cls E)

theorem nb095_wpp_notmem_0515 (f : Var) : f ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb095_compact_fv_empty_0035 f)

theorem nb095_compact_envfresh_0037 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TEnvFresh
      [((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy009 D R S_cls E) (nb095AlphaDummy010 f)
      (nb095_wpp_notmem_0506 D R S_cls E) (nb095_wpp_notmem_0507 f)
      (TEnvFresh.consFresh (nb095AlphaDummy007 D R S_cls E) (nb095AlphaDummy008 f)
        (nb095_wpp_notmem_0508 D R S_cls E) (nb095_wpp_notmem_0509 f)
        (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
          (nb095_wpp_notmem_0510 D R S_cls E) (nb095_wpp_notmem_0511 u)
          (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
            (nb095_wpp_notmem_0512 D R S_cls E) (nb095_wpp_notmem_0513 x)
            (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
              (nb095_wpp_notmem_0514 D R S_cls E) (nb095_wpp_notmem_0515 f)
              (TEnvFresh.nil ((synCid)).fv))))))

/-- Checked nominal proof certificate identified upstream as `nb095_wpp_refl_0035`. -/
@[expose]
noncomputable def nb095WppRefl0035 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TReflOn
      [((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0037 x u D R S_cls f E)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
