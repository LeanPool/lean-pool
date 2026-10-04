/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part028`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0052`. -/
@[expose]
noncomputable def nb068SplitAlpha0052 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
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
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy176))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
          (Class.cv (nb068AlphaDummy175))))
      (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
          (Class.cv (nb068AlphaDummy177 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
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
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                (by
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
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0051 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
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
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                    (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
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
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0053`. -/
@[expose]
noncomputable def nb068SplitAlpha0053 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy197))
          (Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy197))
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy198 f))
          (Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy198 f))
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from
                    (by
                      unfold nb068AlphaDummy168;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                  (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                      unfold nb068AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from
                      (by
                        unfold nb068AlphaDummy167;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                    (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                        unfold nb068AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                          unfold nb068AlphaDummy197;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                          unfold nb068AlphaDummy198;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from (by
                            unfold nb068AlphaDummy171;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                            unfold nb068AlphaDummy172;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy126))).fv ∪
                      ((Class.cv (nb068AlphaDummy125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
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
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0052 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
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
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0052 x y f)))))))))
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
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from
                      (by
                        unfold nb068AlphaDummy168;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                    (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                        unfold nb068AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
                          unfold nb068AlphaDummy167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                          unfold nb068AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                            unfold nb068AlphaDummy197;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                            unfold nb068AlphaDummy198;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from (by
                              unfold nb068AlphaDummy171;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                          (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                              unfold nb068AlphaDummy172;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
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
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
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
                  (nb068_support_mem_0201 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy199)
        from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198)
                  0)))) (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0052 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
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
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
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
                  (nb068_support_mem_0201 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy199)
        from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198)
                  0)))) (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0052 x y f)))))))))
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
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0054`. -/
@[expose]
noncomputable def nb068SplitAlpha0054 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy129))
          (synCop (Class.cv (nb068AlphaDummy125)) (Class.cv (nb068AlphaDummy126))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))))
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy130 f))
          (synCop (Class.cv (nb068AlphaDummy127 f)) (Class.cv (nb068AlphaDummy128 f))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy129) from (by
                unfold nb068AlphaDummy129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0))))) (Ne.symm
            (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy130 f) from (by
                unfold nb068AlphaDummy130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy129) from
                (by
                  unfold nb068AlphaDummy129;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
            (Ne.symm (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy130 f) from (by
                  unfold nb068AlphaDummy130;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                    (by
                                      unfold nb068AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from
                                    (by
                                      unfold nb068AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
                                        unfold nb068AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068AlphaDummy127 f) ≠
                                        (nb068AlphaDummy133 f) from (by
                                        unfold nb068AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from
                                        (by
                                          unfold nb068AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
                                          unfold nb068AlphaDummy138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy135) from (by
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
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0045 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                    (by
                                      unfold nb068AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from
                                    (by
                                      unfold nb068AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
                                        unfold nb068AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068AlphaDummy127 f) ≠
                                        (nb068AlphaDummy133 f) from (by
                                        unfold nb068AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from
                                        (by
                                          unfold nb068AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
                                          unfold nb068AlphaDummy138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy135) from (by
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
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0045 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0048 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                        unfold nb068AlphaDummy168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy170 f) from (by
                                        unfold nb068AlphaDummy170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                        (by
                                          unfold nb068AlphaDummy167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy169 f) from (by
                                          unfold nb068AlphaDummy169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy126) ≠
        (nb068AlphaDummy173) from (by
          unfold nb068AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy174 f) from (by
          unfold nb068AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from (by
          unfold nb068AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
          unfold nb068AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0050 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                        unfold nb068AlphaDummy168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy170 f) from (by
                                        unfold nb068AlphaDummy170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                        (by
                                          unfold nb068AlphaDummy167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy169 f) from (by
                                          unfold nb068AlphaDummy169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy126) ≠
        (nb068AlphaDummy173) from (by
          unfold nb068AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy174 f) from (by
          unfold nb068AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from (by
          unfold nb068AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
          unfold nb068AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0050 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0053 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy126) from (by
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
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy047) from
                    (by
                      unfold nb068AlphaDummy047;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
                  (show f ≠ (nb068AlphaDummy050 f) from (by
                      unfold nb068AlphaDummy050;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy046) from
                      (by
                        unfold nb068AlphaDummy046;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 1))))
                    (show f ≠ (nb068AlphaDummy049 f) from (by
                        unfold nb068AlphaDummy049;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0208 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy045) from (by
                          unfold nb068AlphaDummy045;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0206) 0))))
                      (show f ≠ (nb068AlphaDummy048 f) from (by
                          unfold nb068AlphaDummy048;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0208 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy051) from (by
                            unfold nb068AlphaDummy051;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0207) 0))))
                        (show f ≠ (nb068AlphaDummy052 f) from (by
                            unfold nb068AlphaDummy052;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0209 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0055`. -/
@[expose]
noncomputable def nb068SplitAlpha0055 (x : Var) (y : Var) (f : Var) :
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part029`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0056`. -/
@[expose]
noncomputable def nb068SplitAlpha0056 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
        ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
        ((nb068AlphaDummy209), (nb068AlphaDummy210 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy203))
        (synCphi (Class.cv (nb068AlphaDummy204))))
      (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
        (synCphi (Class.cv (nb068AlphaDummy206 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy050 f))).fv ∪
            ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy211) from (by
                    unfold nb068AlphaDummy211;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 0))))
                (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy213 f) from (by
                    unfold nb068AlphaDummy213;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy204) ≠ (nb068AlphaDummy212) from
                    (by
                      unfold nb068AlphaDummy212;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 1))))
                  (show (nb068AlphaDummy206 f) ≠ (nb068AlphaDummy214 f) from (by
                      unfold nb068AlphaDummy214;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy204))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy206 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy211) ≠ (nb068AlphaDummy218) from
                                    (by
                                      unfold nb068AlphaDummy218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0224)
                                              1)))) (show
                                    (nb068AlphaDummy213 f) ≠ (nb068AlphaDummy221 f) from
                                    (by
                                      unfold nb068AlphaDummy221;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0225 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy211) ≠ (nb068AlphaDummy217) from (by
                                        unfold nb068AlphaDummy217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0224)
                                                0)))) (show (nb068AlphaDummy213 f) ≠
                                        (nb068AlphaDummy220 f) from (by
                                        unfold nb068AlphaDummy220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0225 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy211) ≠ (nb068AlphaDummy215) from
                                        (by
                                          unfold nb068AlphaDummy215;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0222)
                                                  0)))) (show (nb068AlphaDummy213 f) ≠
        (nb068AlphaDummy216 f) from (by
                                          unfold nb068AlphaDummy216;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0223 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
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
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0055 x y f))))))))
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
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
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
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0057`. -/
@[expose]
noncomputable def nb068SplitAlpha0057 (x : Var) (y : Var) (f : Var) :
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0058`. -/
@[expose]
noncomputable def nb068SplitAlpha0058 (x : Var) (y : Var) (f : Var) :
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
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0057 x y f))))))))
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
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0059`. -/
@[expose]
noncomputable def nb068SplitAlpha0059 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy233))
          (Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy233))
            (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy234 f))
          (Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy234 f))
            (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy204) from
                    (by
                      unfold nb068AlphaDummy204;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
                  (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy206 f) from (by
                      unfold nb068AlphaDummy206;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy203) from
                      (by
                        unfold nb068AlphaDummy203;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
                    (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy205 f) from (by
                        unfold nb068AlphaDummy205;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0244 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy233) from (by
                          unfold nb068AlphaDummy233;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0246) 0))))
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy234 f) from (by
                          unfold nb068AlphaDummy234;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0247 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy207) from (by
                            unfold nb068AlphaDummy207;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0243) 0))))
                        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy208 f) from (by
                            unfold nb068AlphaDummy208;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0245 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb068AlphaDummy047))).fv ∪
                      ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy050 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0058 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0058 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                          ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                          ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                          ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                          ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy204) from
                      (by
                        unfold nb068AlphaDummy204;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
                    (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy206 f) from (by
                        unfold nb068AlphaDummy206;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0244 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy203) from (by
                          unfold nb068AlphaDummy203;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0242) 0))))
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy205 f) from (by
                          unfold nb068AlphaDummy205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy233) from (by
                            unfold nb068AlphaDummy233;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0246) 0))))
                        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy234 f) from (by
                            unfold nb068AlphaDummy234;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0247 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy207) from (by
                              unfold nb068AlphaDummy207;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0243) 0))))
                          (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy208 f) from (by
                              unfold nb068AlphaDummy208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0245 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy047))).fv ∪
                        ((Class.cv (nb068AlphaDummy046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy050 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0058 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0058 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                            ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                            ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                            ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                            ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                            ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                            ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                            ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                            ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0060`. -/
@[expose]
noncomputable def nb068SplitAlpha0060 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy045))
          (synCcnv (Class.cv (nb068AlphaDummy000))) (Class.cv (nb068AlphaDummy047)))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy047)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy046)))))
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
          (Class.cv (nb068AlphaDummy050 f))) (Wff.neg
          (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy049 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy090) from
                                    (by
                                      unfold nb068AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0084)
                                              1)))) (show
                                    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy092 f) from
                                    (by
                                      unfold nb068AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0086 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy045) ≠ (nb068AlphaDummy089) from (by
                                        unfold nb068AlphaDummy089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0084)
                                                0)))) (show (nb068AlphaDummy048 f) ≠
                                        (nb068AlphaDummy091 f) from (by
                                        unfold nb068AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0086 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy045) ≠ (nb068AlphaDummy095) from
                                        (by
                                          unfold nb068AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0088)
                                                  0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy096 f) from (by
                                          unfold nb068AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0089 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy045) ≠
        (nb068AlphaDummy093) from (by
          unfold nb068AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0085) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy094 f) from (by
          unfold nb068AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0087 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb068SplitAlpha0040 x y f)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy090) from
                                    (by
                                      unfold nb068AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0084)
                                              1)))) (show
                                    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy092 f) from
                                    (by
                                      unfold nb068AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0086 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy045) ≠ (nb068AlphaDummy089) from (by
                                        unfold nb068AlphaDummy089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0084)
                                                0)))) (show (nb068AlphaDummy048 f) ≠
                                        (nb068AlphaDummy091 f) from (by
                                        unfold nb068AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0086 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy045) ≠ (nb068AlphaDummy095) from
                                        (by
                                          unfold nb068AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0088)
                                                  0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy096 f) from (by
                                          unfold nb068AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0089 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy045) ≠
        (nb068AlphaDummy093) from (by
          unfold nb068AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0085) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy094 f) from (by
          unfold nb068AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0087 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb068SplitAlpha0040 x y f)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0043 x y f))))))))
      (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0054 x y f))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy047) ≠ (nb068AlphaDummy204) from (by
                                        unfold nb068AlphaDummy204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0214)
                                                1)))) (show (nb068AlphaDummy050 f) ≠
                                        (nb068AlphaDummy206 f) from (by
                                        unfold nb068AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy047) ≠ (nb068AlphaDummy203) from
                                        (by
                                          unfold nb068AlphaDummy203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0214)
                                                  0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy205 f) from (by
                                          unfold nb068AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy047) ≠
        (nb068AlphaDummy209) from (by
          unfold nb068AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0218) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy210 f) from (by
          unfold nb068AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy047) ≠ (nb068AlphaDummy207) from (by
          unfold nb068AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0215) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy208 f) from (by
          unfold nb068AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (nb068SplitAlpha0056 x y f)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy047) ≠ (nb068AlphaDummy204) from (by
                                        unfold nb068AlphaDummy204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0214)
                                                1)))) (show (nb068AlphaDummy050 f) ≠
                                        (nb068AlphaDummy206 f) from (by
                                        unfold nb068AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy047) ≠ (nb068AlphaDummy203) from
                                        (by
                                          unfold nb068AlphaDummy203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0214)
                                                  0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy205 f) from (by
                                          unfold nb068AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy047) ≠
        (nb068AlphaDummy209) from (by
          unfold nb068AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0218) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy210 f) from (by
          unfold nb068AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy047) ≠ (nb068AlphaDummy207) from (by
          unfold nb068AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0215) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy208 f) from (by
          unfold nb068AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (nb068SplitAlpha0056 x y f)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0059 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy047) from (by
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
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 1))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy045) from (by
                    unfold nb068AlphaDummy045;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 0))))
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
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0209 f) 0))))
                  (TAlphaVar.here _ _ _)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part030`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0061`. -/
@[expose]
noncomputable def nb068SplitAlpha0061 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy259), (nb068AlphaDummy262 f)),
        ((nb068AlphaDummy258), (nb068AlphaDummy261 f)),
        ((nb068AlphaDummy257), (nb068AlphaDummy260 f)),
        ((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
        ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
        ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
        ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
        ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
        ((nb068AlphaDummy249), (nb068AlphaDummy250 f)),
        ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy257))
            (synCun (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy260 f))
            (synCun (Class.cv (nb068AlphaDummy261 f))
              (Class.cv (nb068AlphaDummy262 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0266) 0))))
                          (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0267 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0264) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0265 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0270) 0))))
                          (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0271 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0268) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0269 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0266) 0))))
                          (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0267 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0264) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0265 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0270) 0))))
                          (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0271 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0268) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0269 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy259), (nb068AlphaDummy262 f)),
          ((nb068AlphaDummy258), (nb068AlphaDummy261 f)),
          ((nb068AlphaDummy257), (nb068AlphaDummy260 f)),
          ((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
          ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
          ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
          ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
          ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
          ((nb068AlphaDummy249), (nb068AlphaDummy250 f)),
          ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy269) from (by
                                unfold nb068AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0274) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy270 f) from (by
                                unfold nb068AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0275 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0272) 0))))
                              (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0273 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy269) from (by
                                unfold nb068AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0274) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy270 f) from (by
                                unfold nb068AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0275 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0272) 0))))
                              (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0273 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy271) from (by
                                unfold nb068AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0278) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy272 f) from (by
                                unfold nb068AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0279 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0276) 0))))
                              (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0277 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy271) from (by
                                unfold nb068AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0278) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy272 f) from (by
                                unfold nb068AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0279 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0276) 0))))
                              (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0277 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0062`. -/
@[expose]
noncomputable def nb068SplitAlpha0062 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
        ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
        ((nb068AlphaDummy249), (nb068AlphaDummy250 f)),
        ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy243))
        (synCphi (Class.cv (nb068AlphaDummy244))))
      (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
        (synCphi (Class.cv (nb068AlphaDummy246 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy242 f))).fv ∪
            ((Class.cv (nb068AlphaDummy241 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy244) ≠ (nb068AlphaDummy251) from (by
                    unfold nb068AlphaDummy251;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0258) 0))))
                (show (nb068AlphaDummy246 f) ≠ (nb068AlphaDummy253 f) from (by
                    unfold nb068AlphaDummy253;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0259 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy244) ≠ (nb068AlphaDummy252) from
                    (by
                      unfold nb068AlphaDummy252;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0258) 1))))
                  (show (nb068AlphaDummy246 f) ≠ (nb068AlphaDummy254 f) from (by
                      unfold nb068AlphaDummy254;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0259 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy244))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy246 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy258) from
                                    (by
                                      unfold nb068AlphaDummy258;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0262)
                                              1)))) (show
                                    (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy261 f) from
                                    (by
                                      unfold nb068AlphaDummy261;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0263 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy251) ≠ (nb068AlphaDummy257) from (by
                                        unfold nb068AlphaDummy257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0262)
                                                0)))) (show (nb068AlphaDummy253 f) ≠
                                        (nb068AlphaDummy260 f) from (by
                                        unfold nb068AlphaDummy260;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0263 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from
                                        (by
                                          unfold nb068AlphaDummy255;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0260)
                                                  0)))) (show (nb068AlphaDummy253 f) ≠
        (nb068AlphaDummy256 f) from (by
                                          unfold nb068AlphaDummy256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0261 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb068AlphaDummy259), (nb068AlphaDummy262 f)),
                                      ((nb068AlphaDummy258), (nb068AlphaDummy261 f)),
                                      ((nb068AlphaDummy257), (nb068AlphaDummy260 f)),
                                      ((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
                                      ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
                                      ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
                                      ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                                      ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                                      ((nb068AlphaDummy249), (nb068AlphaDummy250 f)),
                                      ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0061 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from (by
                              unfold nb068AlphaDummy255;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0260) 0))))
                          (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from (by
                              unfold nb068AlphaDummy256;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0261 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
                          ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
                          ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
                          ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                          ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                          ((nb068AlphaDummy249), (nb068AlphaDummy250 f)),
                          ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from (by
                            unfold nb068AlphaDummy255;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0260) 0))))
                        (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from (by
                            unfold nb068AlphaDummy256;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0261 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from (by
                              unfold nb068AlphaDummy255;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0260) 0))))
                          (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from (by
                              unfold nb068AlphaDummy256;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0261 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
                          ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
                          ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
                          ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                          ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                          ((nb068AlphaDummy249), (nb068AlphaDummy250 f)),
                          ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0063`. -/
@[expose]
noncomputable def nb068SplitAlpha0063 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy259), (nb068AlphaDummy262 f)),
        ((nb068AlphaDummy258), (nb068AlphaDummy261 f)),
        ((nb068AlphaDummy257), (nb068AlphaDummy260 f)),
        ((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
        ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
        ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
        ((nb068AlphaDummy277), (nb068AlphaDummy278 f)),
        ((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
        ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
        ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
        ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
        ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy257))
            (synCun (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy260 f))
            (synCun (Class.cv (nb068AlphaDummy261 f))
              (Class.cv (nb068AlphaDummy262 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0266) 0))))
                          (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0267 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0264) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0265 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0270) 0))))
                          (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0271 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0268) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0269 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0266) 0))))
                          (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0267 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0264) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0265 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy265) from (by
                              unfold nb068AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0270) 0))))
                          (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy266 f) from (by
                              unfold nb068AlphaDummy266;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0271 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy263) from (by
                                unfold nb068AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0268) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy264 f) from (by
                                unfold nb068AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0269 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy259), (nb068AlphaDummy262 f)),
          ((nb068AlphaDummy258), (nb068AlphaDummy261 f)),
          ((nb068AlphaDummy257), (nb068AlphaDummy260 f)),
          ((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
          ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
          ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
          ((nb068AlphaDummy277), (nb068AlphaDummy278 f)),
          ((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
          ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
          ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
          ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
          ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy269) from (by
                                unfold nb068AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0274) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy270 f) from (by
                                unfold nb068AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0275 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0272) 0))))
                              (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0273 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy269) from (by
                                unfold nb068AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0274) 0))))
                            (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy270 f) from (by
                                unfold nb068AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0275 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy258) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0272) 0))))
                              (show (nb068AlphaDummy261 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0273 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy271) from (by
                                unfold nb068AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0278) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy272 f) from (by
                                unfold nb068AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0279 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0276) 0))))
                              (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0277 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy271) from (by
                                unfold nb068AlphaDummy271;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0278) 0))))
                            (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy272 f) from (by
                                unfold nb068AlphaDummy272;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0279 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy259) ≠ (nb068AlphaDummy267) from (by
                                  unfold nb068AlphaDummy267;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0276) 0))))
                              (show (nb068AlphaDummy262 f) ≠ (nb068AlphaDummy268 f) from
                                (by
                                  unfold nb068AlphaDummy268;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0277 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part031`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0064`. -/
@[expose]
noncomputable def nb068SplitAlpha0064 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
        ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
        ((nb068AlphaDummy277), (nb068AlphaDummy278 f)),
        ((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
        ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
        ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
        ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
        ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy251))
          (Class.cv (nb068AlphaDummy244))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy252))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy251)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy251)) (synC1c))
              (Class.cv (nb068AlphaDummy251))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy253 f))
          (Class.cv (nb068AlphaDummy246 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy254 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy253 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy253 f)) (synC1c))
              (Class.cv (nb068AlphaDummy253 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy244) ≠ (nb068AlphaDummy251) from (by
              unfold nb068AlphaDummy251;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0258) 0))))
          (show (nb068AlphaDummy246 f) ≠ (nb068AlphaDummy253 f) from (by
              unfold nb068AlphaDummy253;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0259 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy244) ≠ (nb068AlphaDummy252) from (by
                unfold nb068AlphaDummy252;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0258) 1))))
            (show (nb068AlphaDummy246 f) ≠ (nb068AlphaDummy254 f) from (by
                unfold nb068AlphaDummy254;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0259 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy244) ≠ (nb068AlphaDummy277) from (by
                  unfold nb068AlphaDummy277;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0288) 0))))
              (show (nb068AlphaDummy246 f) ≠ (nb068AlphaDummy278 f) from (by
                  unfold nb068AlphaDummy278;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0289 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy244) ≠ (nb068AlphaDummy275) from (by
                    unfold nb068AlphaDummy275;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0286) 0))))
                (show (nb068AlphaDummy246 f) ≠ (nb068AlphaDummy276 f) from (by
                    unfold nb068AlphaDummy276;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0287 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy244))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy246 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy258) from (by
                                  unfold nb068AlphaDummy258;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0262) 1))))
                              (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy261 f) from
                                (by
                                  unfold nb068AlphaDummy261;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0263 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy257) from (by
                                    unfold nb068AlphaDummy257;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0262) 0)))) (show
                                  (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy260 f) from (by
                                    unfold nb068AlphaDummy260;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0263 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from
                                    (by
                                      unfold nb068AlphaDummy255;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0260)
                                              0)))) (show
                                    (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from
                                    (by
                                      unfold nb068AlphaDummy256;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0261 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy259), (nb068AlphaDummy262 f)),
                                  ((nb068AlphaDummy258), (nb068AlphaDummy261 f)),
                                  ((nb068AlphaDummy257), (nb068AlphaDummy260 f)),
                                  ((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
                                  ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
                                  ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
                                  ((nb068AlphaDummy277), (nb068AlphaDummy278 f)),
                                  ((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
                                  ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                                  ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                                  ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
                                  ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                                  ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                                  ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0063 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from (by
                          unfold nb068AlphaDummy255;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0260) 0))))
                      (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from (by
                          unfold nb068AlphaDummy256;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0261 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
                      ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
                      ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
                      ((nb068AlphaDummy277), (nb068AlphaDummy278 f)),
                      ((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
                      ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                      ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                      ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
                      ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from
                      (by
                        unfold nb068AlphaDummy255;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0260) 0))))
                    (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from (by
                        unfold nb068AlphaDummy256;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0261 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy251) ≠ (nb068AlphaDummy255) from (by
                          unfold nb068AlphaDummy255;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0260) 0))))
                      (show (nb068AlphaDummy253 f) ≠ (nb068AlphaDummy256 f) from (by
                          unfold nb068AlphaDummy256;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0261 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy255), (nb068AlphaDummy256 f)),
                      ((nb068AlphaDummy251), (nb068AlphaDummy253 f)),
                      ((nb068AlphaDummy252), (nb068AlphaDummy254 f)),
                      ((nb068AlphaDummy277), (nb068AlphaDummy278 f)),
                      ((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
                      ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                      ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                      ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
                      ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0065`. -/
@[expose]
noncomputable def nb068SplitAlpha0065 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
        ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy273))
          (Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy273))
            (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy274 f))
          (Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy274 f))
            (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy244) from
                    (by
                      unfold nb068AlphaDummy244;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))))
                  (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy246 f) from (by
                      unfold nb068AlphaDummy246;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy243) from
                      (by
                        unfold nb068AlphaDummy243;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))))
                    (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy245 f) from (by
                        unfold nb068AlphaDummy245;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0282 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy273) from (by
                          unfold nb068AlphaDummy273;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0284) 0))))
                      (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy274 f) from (by
                          unfold nb068AlphaDummy274;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0285 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy247) from (by
                            unfold nb068AlphaDummy247;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0281) 0))))
                        (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy248 f) from (by
                            unfold nb068AlphaDummy248;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0283 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
                              ((synCvv)).fv) (by decide)) (freshVar_injective
                            (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy240))).fv ∪
                      ((Class.cv (nb068AlphaDummy239))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy242 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy241 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0064 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0064 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
                          ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                          ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                          ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
                          ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy244) from
                      (by
                        unfold nb068AlphaDummy244;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))))
                    (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy246 f) from (by
                        unfold nb068AlphaDummy246;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0282 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy243) from (by
                          unfold nb068AlphaDummy243;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0280) 0))))
                      (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy245 f) from (by
                          unfold nb068AlphaDummy245;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0282 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy273) from (by
                            unfold nb068AlphaDummy273;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0284) 0))))
                        (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy274 f) from (by
                            unfold nb068AlphaDummy274;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0285 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy247) from (by
                              unfold nb068AlphaDummy247;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0281) 0))))
                          (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy248 f) from (by
                              unfold nb068AlphaDummy248;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0283 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪
                                ((synCvv)).fv) (by decide)) (freshVar_injective
                              (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy240))).fv ∪
                        ((Class.cv (nb068AlphaDummy239))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy242 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy241 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0064 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0064 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy275), (nb068AlphaDummy276 f)),
                            ((nb068AlphaDummy244), (nb068AlphaDummy246 f)),
                            ((nb068AlphaDummy243), (nb068AlphaDummy245 f)),
                            ((nb068AlphaDummy273), (nb068AlphaDummy274 f)),
                            ((nb068AlphaDummy247), (nb068AlphaDummy248 f)),
                            ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                            ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0066`. -/
@[expose]
noncomputable def nb068SplitAlpha0066 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy145))
            (synCun (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy148 f))
            (synCun (Class.cv (nb068AlphaDummy149 f))
              (Class.cv (nb068AlphaDummy150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0067`. -/
@[expose]
noncomputable def nb068SplitAlpha0067 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy139))
            (Class.cv (nb068AlphaDummy132))) (Wff.classEq (Class.cv (nb068AlphaDummy140))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
              (Class.cv (nb068AlphaDummy139))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy141 f))
            (Class.cv (nb068AlphaDummy134 f)))
          (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
              (Class.cv (nb068AlphaDummy141 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
                unfold nb068AlphaDummy139;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0))))
            (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy141 f) from (by
                unfold nb068AlphaDummy141;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
                  unfold nb068AlphaDummy140;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1))))
              (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy142 f) from (by
                  unfold nb068AlphaDummy142;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                                  unfold nb068AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from
                                (by
                                  unfold nb068AlphaDummy149;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy145) from (by
                                    unfold nb068AlphaDummy145;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0136) 0)))) (show
                                  (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                    unfold nb068AlphaDummy148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0137 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                                    (by
                                      unfold nb068AlphaDummy143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0134)
                                              0)))) (show
                                    (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                    (by
                                      unfold nb068AlphaDummy144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0135 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                                  ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                                  ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                                  ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                                  ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                                  ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0066 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                          unfold nb068AlphaDummy143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                          unfold nb068AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                      ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                      ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                      ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                      ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                      ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                      ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                      (by
                        unfold nb068AlphaDummy143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                    (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                        unfold nb068AlphaDummy144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                          unfold nb068AlphaDummy143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                          unfold nb068AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                      ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                      ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                      ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                      ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                      ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                      ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
