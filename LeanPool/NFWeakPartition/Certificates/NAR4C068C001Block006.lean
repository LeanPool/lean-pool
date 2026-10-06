/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part021`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0023`. -/
@[expose]
noncomputable def nb068SplitAlpha0023 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy179))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy179)) (Class.cv (nb068AlphaDummy175)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy180 f))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy180 f))
            (Class.cv (nb068AlphaDummy177 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                          unfold nb068AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from (by
                          unfold nb068AlphaDummy185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                            unfold nb068AlphaDummy181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                        (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                            unfold nb068AlphaDummy184;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                              unfold nb068AlphaDummy179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                          (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                              unfold nb068AlphaDummy180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                          ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                          ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                          ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                          ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0022 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                  unfold nb068AlphaDummy179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                  unfold nb068AlphaDummy180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
              ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
              ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
              ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
              ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
              ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
              ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
              ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
              ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
              ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
              ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
              ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
              ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
              ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
              ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                unfold nb068AlphaDummy179;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
            (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                unfold nb068AlphaDummy180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                  unfold nb068AlphaDummy179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                  unfold nb068AlphaDummy180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
              ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
              ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
              ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
              ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
              ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
              ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
              ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
              ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
              ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
              ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
              ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
              ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
              ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
              ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0024`. -/
@[expose]
noncomputable def nb068SplitAlpha0024 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.neg (Wff.all (nb068AlphaDummy168) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb068AlphaDummy168))
                (Class.cv (nb068AlphaDummy125)))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168))) (synCsn (synC0c))))))))
      (Wff.neg (Wff.all (nb068AlphaDummy170 f) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb068AlphaDummy170 f))
                (Class.cv (nb068AlphaDummy127 f)))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from (by
                unfold nb068AlphaDummy168;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
            (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                unfold nb068AlphaDummy170;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
                  unfold nb068AlphaDummy167;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
              (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                  unfold nb068AlphaDummy169;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                    unfold nb068AlphaDummy197;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                    unfold nb068AlphaDummy198;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from
                    (by
                      unfold nb068AlphaDummy171;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                  (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                      unfold nb068AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                      (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy126))).fv ∪
                ((Class.cv (nb068AlphaDummy125))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                                        unfold nb068AlphaDummy175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068AlphaDummy170 f) ≠
                                        (nb068AlphaDummy177 f) from (by
                                        unfold nb068AlphaDummy177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from
                                        (by
                                          unfold nb068AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
                                          unfold nb068AlphaDummy178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068SplitAlpha0023 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                                        unfold nb068AlphaDummy175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068AlphaDummy170 f) ≠
                                        (nb068AlphaDummy177 f) from (by
                                        unfold nb068AlphaDummy177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from
                                        (by
                                          unfold nb068AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
                                          unfold nb068AlphaDummy178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068SplitAlpha0023 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                    ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                    ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                    ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                    ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                    ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                    ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                    ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                    ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                    ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                    ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                    ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                    ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                    ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                    ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                    ((nb068AlphaDummy001), x),
                    ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0025`. -/
@[expose]
noncomputable def nb068SplitAlpha0025 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classMem
        (synCop (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy125)))
        (Class.cv (nb068AlphaDummy000)))
      (Wff.classMem (synCop (Class.cv (nb068AlphaDummy128 f))
          (Class.cv (nb068AlphaDummy127 f))) (Class.cv f)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                    unfold nb068AlphaDummy168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
                                    unfold nb068AlphaDummy170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                    (by
                                      unfold nb068AlphaDummy167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from
                                    (by
                                      unfold nb068AlphaDummy169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy173) from (by
                                        unfold nb068AlphaDummy173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy174 f) from (by
                                        unfold nb068AlphaDummy174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from
                                        (by
                                          unfold nb068AlphaDummy171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
                                          unfold nb068AlphaDummy172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy126))).fv ∪
                                    ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                    ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068SplitAlpha0021 x y f)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                    unfold nb068AlphaDummy168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
                                    unfold nb068AlphaDummy170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                    (by
                                      unfold nb068AlphaDummy167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from
                                    (by
                                      unfold nb068AlphaDummy169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy173) from (by
                                        unfold nb068AlphaDummy173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy174 f) from (by
                                        unfold nb068AlphaDummy174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from
                                        (by
                                          unfold nb068AlphaDummy171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
                                          unfold nb068AlphaDummy172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy126))).fv ∪
                                    ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                    ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068SplitAlpha0021 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (nb068SplitAlpha0024 x y f)))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (nb068SplitAlpha0024 x y f)))))))))) (TAlphaClass.cv
      (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy126) from (by
            unfold nb068AlphaDummy126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
        (show f ≠ (nb068AlphaDummy128 f) from (by
            unfold nb068AlphaDummy128;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
        (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy125) from (by
              unfold nb068AlphaDummy125;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
          (show f ≠ (nb068AlphaDummy127 f) from (by
              unfold nb068AlphaDummy127;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy129) from (by
                unfold nb068AlphaDummy129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0))))
            (show f ≠ (nb068AlphaDummy130 f) from (by
                unfold nb068AlphaDummy130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy047) from (by
                  unfold nb068AlphaDummy047;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
              (show f ≠ (nb068AlphaDummy050 f) from (by
                  unfold nb068AlphaDummy050;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy046) from (by
                    unfold nb068AlphaDummy046;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 1))))
                (show f ≠ (nb068AlphaDummy049 f) from (by
                    unfold nb068AlphaDummy049;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 1))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy045) from
                    (by
                      unfold nb068AlphaDummy045;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 0))))
                  (show f ≠ (nb068AlphaDummy048 f) from (by
                      unfold nb068AlphaDummy048;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 0))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy051) from
                      (by
                        unfold nb068AlphaDummy051;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0207) 0))))
                    (show f ≠ (nb068AlphaDummy052 f) from (by
                        unfold nb068AlphaDummy052;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0209 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy043) from (by
                          unfold nb068AlphaDummy043;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0204) 0))))
                      (show f ≠ (nb068AlphaDummy044 f) from (by
                          unfold nb068AlphaDummy044;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0205 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy041) from (by
                            unfold nb068AlphaDummy041;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0202) 0))))
                        (show f ≠ (nb068AlphaDummy042 f) from (by
                            unfold nb068AlphaDummy042;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0203 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0026`. -/
@[expose]
noncomputable def nb068SplitAlpha0026 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.all (nb068AlphaDummy126) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb068AlphaDummy129))
              (synCop (Class.cv (nb068AlphaDummy125)) (Class.cv (nb068AlphaDummy126))))
            (synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy125))))))
      (Wff.all (nb068AlphaDummy128 f) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb068AlphaDummy130 f))
              (synCop (Class.cv (nb068AlphaDummy127 f))
                (Class.cv (nb068AlphaDummy128 f))))
            (synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
              (Class.cv (nb068AlphaDummy127 f)))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (Ne.symm
                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy129) from (by
                    unfold nb068AlphaDummy129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0)))))
              (Ne.symm (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy130 f) from (by
                    unfold nb068AlphaDummy130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
              (TAlphaVar.there (Ne.symm
                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy129) from (by
                      unfold nb068AlphaDummy129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
                (Ne.symm (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy130 f) from (by
                      unfold nb068AlphaDummy130;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                        (by
                                          unfold nb068AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy134 f) from (by
                                          unfold nb068AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from (by
          unfold nb068AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
          unfold nb068AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy125))).fv ∪
        ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068SplitAlpha0016 x y f)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                        (by
                                          unfold nb068AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy134 f) from (by
                                          unfold nb068AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from (by
          unfold nb068AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
          unfold nb068AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy125))).fv ∪
        ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068SplitAlpha0016 x y f)))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0019 x y f)))))))))
        (nb068SplitAlpha0025 x y f))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part022`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0027`. -/
@[expose]
noncomputable def nb068SplitAlpha0027 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy219), (nb068AlphaDummy222 f)),
        ((nb068AlphaDummy218), (nb068AlphaDummy221 f)),
        ((nb068AlphaDummy217), (nb068AlphaDummy220 f)),
        ((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
        ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
        ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
        ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
        ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
        ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy217))
            (synCun (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy220 f))
            (synCun (Class.cv (nb068AlphaDummy221 f))
              (Class.cv (nb068AlphaDummy222 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy219), (nb068AlphaDummy222 f)),
          ((nb068AlphaDummy218), (nb068AlphaDummy221 f)),
          ((nb068AlphaDummy217), (nb068AlphaDummy220 f)),
          ((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
          ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
          ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
          ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
          ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
          ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
          ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
          ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
          ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy229) from (by
                                unfold nb068AlphaDummy229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy230 f) from (by
                                unfold nb068AlphaDummy230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy229) from (by
                                unfold nb068AlphaDummy229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy230 f) from (by
                                unfold nb068AlphaDummy230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy231) from (by
                                unfold nb068AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy232 f) from (by
                                unfold nb068AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy231) from (by
                                unfold nb068AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy232 f) from (by
                                unfold nb068AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0028`. -/
@[expose]
noncomputable def nb068SplitAlpha0028 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
        ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
        ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
        ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
        ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy211))
          (Class.cv (nb068AlphaDummy204))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy212))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy211)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy211)) (synC1c))
              (Class.cv (nb068AlphaDummy211))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy213 f))
          (Class.cv (nb068AlphaDummy206 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy214 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy213 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy213 f)) (synC1c))
              (Class.cv (nb068AlphaDummy213 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy211) from (by
              unfold nb068AlphaDummy211;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 0))))
          (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy213 f) from (by
              unfold nb068AlphaDummy213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy212) from (by
                unfold nb068AlphaDummy212;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 1))))
            (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy214 f) from (by
                unfold nb068AlphaDummy214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy204))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy206 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy218) from (by
                                  unfold nb068AlphaDummy218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0224) 1))))
                              (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy221 f) from
                                (by
                                  unfold nb068AlphaDummy221;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy217) from (by
                                    unfold nb068AlphaDummy217;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0224) 0)))) (show
                                  (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy220 f) from (by
                                    unfold nb068AlphaDummy220;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from
                                    (by
                                      unfold nb068AlphaDummy215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0222)
                                              0)))) (show
                                    (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from
                                    (by
                                      unfold nb068AlphaDummy216;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy219), (nb068AlphaDummy222 f)),
                                  ((nb068AlphaDummy218), (nb068AlphaDummy221 f)),
                                  ((nb068AlphaDummy217), (nb068AlphaDummy220 f)),
                                  ((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
                                  ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
                                  ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
                                  ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                                  ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                                  ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
                                  ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                                  ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                                  ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                  ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                  ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                  ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                                  ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0027 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from (by
                          unfold nb068AlphaDummy215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from (by
                          unfold nb068AlphaDummy216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
                      ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
                      ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
                      ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                      ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                      ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
                      ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                      ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from
                      (by
                        unfold nb068AlphaDummy215;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                    (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from (by
                        unfold nb068AlphaDummy216;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from (by
                          unfold nb068AlphaDummy215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from (by
                          unfold nb068AlphaDummy216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
                      ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
                      ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
                      ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                      ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                      ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
                      ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                      ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0029`. -/
@[expose]
noncomputable def nb068SplitAlpha0029 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy219), (nb068AlphaDummy222 f)),
        ((nb068AlphaDummy218), (nb068AlphaDummy221 f)),
        ((nb068AlphaDummy217), (nb068AlphaDummy220 f)),
        ((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
        ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
        ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
        ((nb068AlphaDummy237), (nb068AlphaDummy238 f)),
        ((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
        ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
        ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
        ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy217))
            (synCun (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy220 f))
            (synCun (Class.cv (nb068AlphaDummy221 f))
              (Class.cv (nb068AlphaDummy222 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy225) from (by
                              unfold nb068AlphaDummy225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy226 f) from (by
                              unfold nb068AlphaDummy226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy223) from (by
                                unfold nb068AlphaDummy223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy224 f) from (by
                                unfold nb068AlphaDummy224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy219), (nb068AlphaDummy222 f)),
          ((nb068AlphaDummy218), (nb068AlphaDummy221 f)),
          ((nb068AlphaDummy217), (nb068AlphaDummy220 f)),
          ((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
          ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
          ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
          ((nb068AlphaDummy237), (nb068AlphaDummy238 f)),
          ((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
          ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
          ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
          ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
          ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
          ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
          ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy229) from (by
                                unfold nb068AlphaDummy229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy230 f) from (by
                                unfold nb068AlphaDummy230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy229) from (by
                                unfold nb068AlphaDummy229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy230 f) from (by
                                unfold nb068AlphaDummy230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy218) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068AlphaDummy221 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy231) from (by
                                unfold nb068AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy232 f) from (by
                                unfold nb068AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy231) from (by
                                unfold nb068AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy232 f) from (by
                                unfold nb068AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy219) ≠ (nb068AlphaDummy227) from (by
                                  unfold nb068AlphaDummy227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068AlphaDummy222 f) ≠ (nb068AlphaDummy228 f) from
                                (by
                                  unfold nb068AlphaDummy228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0030`. -/
@[expose]
noncomputable def nb068SplitAlpha0030 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
        ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
        ((nb068AlphaDummy237), (nb068AlphaDummy238 f)),
        ((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
        ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
        ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
        ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy211))
          (Class.cv (nb068AlphaDummy204))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy212))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy211)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy211)) (synC1c))
              (Class.cv (nb068AlphaDummy211))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy213 f))
          (Class.cv (nb068AlphaDummy206 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy214 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy213 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy213 f)) (synC1c))
              (Class.cv (nb068AlphaDummy213 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy211) from (by
              unfold nb068AlphaDummy211;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 0))))
          (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy213 f) from (by
              unfold nb068AlphaDummy213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy212) from (by
                unfold nb068AlphaDummy212;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 1))))
            (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy214 f) from (by
                unfold nb068AlphaDummy214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy237) from (by
                  unfold nb068AlphaDummy237;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0250) 0))))
              (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy238 f) from (by
                  unfold nb068AlphaDummy238;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0251 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy235) from (by
                    unfold nb068AlphaDummy235;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0248) 0))))
                (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy236 f) from (by
                    unfold nb068AlphaDummy236;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0249 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy204))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy206 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy218) from (by
                                  unfold nb068AlphaDummy218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0224) 1))))
                              (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy221 f) from
                                (by
                                  unfold nb068AlphaDummy221;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy217) from (by
                                    unfold nb068AlphaDummy217;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0224) 0)))) (show
                                  (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy220 f) from (by
                                    unfold nb068AlphaDummy220;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from
                                    (by
                                      unfold nb068AlphaDummy215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0222)
                                              0)))) (show
                                    (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from
                                    (by
                                      unfold nb068AlphaDummy216;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy219), (nb068AlphaDummy222 f)),
                                  ((nb068AlphaDummy218), (nb068AlphaDummy221 f)),
                                  ((nb068AlphaDummy217), (nb068AlphaDummy220 f)),
                                  ((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
                                  ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
                                  ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
                                  ((nb068AlphaDummy237), (nb068AlphaDummy238 f)),
                                  ((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                                  ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                                  ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                                  ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                                  ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                                  ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                                  ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                  ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                  ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                  ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                                  ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0029 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from (by
                          unfold nb068AlphaDummy215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from (by
                          unfold nb068AlphaDummy216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
                      ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
                      ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
                      ((nb068AlphaDummy237), (nb068AlphaDummy238 f)),
                      ((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                      ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                      ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                      ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                      ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                      ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from
                      (by
                        unfold nb068AlphaDummy215;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                    (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from (by
                        unfold nb068AlphaDummy216;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from (by
                          unfold nb068AlphaDummy215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy216 f) from (by
                          unfold nb068AlphaDummy216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy215), (nb068AlphaDummy216 f)),
                      ((nb068AlphaDummy211), (nb068AlphaDummy213 f)),
                      ((nb068AlphaDummy212), (nb068AlphaDummy214 f)),
                      ((nb068AlphaDummy237), (nb068AlphaDummy238 f)),
                      ((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                      ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                      ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                      ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                      ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                      ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
