/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C068C001Part023Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part023`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_wpp_refl_0042`. -/
@[expose]
noncomputable def nb068WppRefl0042 (x : Var) (y : Var) (f : Var) :
    TReflOn
      [((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0042 x y f)

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0033`. -/
@[expose]
noncomputable def nb068SplitAlpha0033 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy041), (nb068AlphaDummy042 f)), ((nb068AlphaDummy000), f),
        ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy041)) (synCnin
            (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy041)) (synCnin
              (synCcom (Class.cv (nb068AlphaDummy000))
                (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid)))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy042 f))
          (synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy042 f))
            (synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (Ne.symm
                              (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy051) from (by
                                  unfold nb068AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0044) 0)))))
                            (Ne.symm (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy052 f)
                                from (by
                                  unfold nb068AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0045 f) 0)))))
                            (TAlphaVar.there (Ne.symm
                                (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy051) from (by
                                    unfold nb068AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0042) 0)))))
                              (Ne.symm (show
                                  (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy052 f) from (by
                                    unfold nb068AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0043 f)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
          unfold nb068AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy056 f) from (by
          unfold nb068AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy053)
        from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy059)
        from (by
          unfold nb068AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy060 f) from (by
          unfold nb068AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy057)
        from (by
          unfold
            nb068AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy058 f) from (by
          unfold
            nb068AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
        ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068SplitAlpha0006 x y f))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
          unfold nb068AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy056 f) from (by
          unfold nb068AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy053)
        from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy059)
        from (by
          unfold nb068AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy060 f) from (by
          unfold nb068AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy057)
        from (by
          unfold
            nb068AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy058 f) from (by
          unfold
            nb068AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
        ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068SplitAlpha0006 x y f)))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb068SplitAlpha0009 x y f)))))))))
                      (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0032 x y f))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                  ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCid) (nb068WppRefl0042 x y f))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                            (TAlphaVar.there (Ne.symm
                                (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy051) from (by
                                    unfold nb068AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0044) 0)))))
                              (Ne.symm (show
                                  (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy052 f) from (by
                                    unfold nb068AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0045 f)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy051) from
                                    (by
                                      unfold nb068AlphaDummy051;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0042)
                                              0))))) (Ne.symm (show
                                    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy052 f) from
                                    (by
                                      unfold nb068AlphaDummy052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0043 f)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
          unfold nb068AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy056 f) from (by
          unfold nb068AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy053)
        from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy059)
        from (by
          unfold
            nb068AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy060 f) from (by
          unfold
            nb068AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy057)
        from (by
          unfold
            nb068AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy058 f) from (by
          unfold
            nb068AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
        ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068SplitAlpha0006 x y f))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
          unfold nb068AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy056 f) from (by
          unfold nb068AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy053)
        from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy059)
        from (by
          unfold
            nb068AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy060 f) from (by
          unfold
            nb068AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy057)
        from (by
          unfold
            nb068AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy058 f) from (by
          unfold
            nb068AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
        ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068SplitAlpha0006 x y f))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb068SplitAlpha0009 x y f)))))))))
                        (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0032 x y f))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn
                  [((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                    ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                    ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                    ((nb068AlphaDummy001), x),
                    ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                  (synCid) (nb068WppRefl0042 x y f)))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0034`. -/
@[expose]
noncomputable def nb068SplitAlpha0034 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy069), (nb068AlphaDummy072 f)),
        ((nb068AlphaDummy068), (nb068AlphaDummy071 f)),
        ((nb068AlphaDummy067), (nb068AlphaDummy070 f)),
        ((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
        ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
        ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
        ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
        ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
        ((nb068AlphaDummy059), (nb068AlphaDummy060 f)),
        ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy067))
            (synCun (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy070 f))
            (synCun (Class.cv (nb068AlphaDummy071 f))
              (Class.cv (nb068AlphaDummy072 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy069), (nb068AlphaDummy072 f)),
          ((nb068AlphaDummy068), (nb068AlphaDummy071 f)),
          ((nb068AlphaDummy067), (nb068AlphaDummy070 f)),
          ((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
          ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
          ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
          ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
          ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
          ((nb068AlphaDummy059), (nb068AlphaDummy060 f)),
          ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy079) from (by
                                unfold nb068AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy080 f) from (by
                                unfold nb068AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy079) from (by
                                unfold nb068AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy080 f) from (by
                                unfold nb068AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy081) from (by
                                unfold nb068AlphaDummy081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy082 f) from (by
                                unfold nb068AlphaDummy082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy081) from (by
                                unfold nb068AlphaDummy081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy082 f) from (by
                                unfold nb068AlphaDummy082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0035`. -/
@[expose]
noncomputable def nb068SplitAlpha0035 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
        ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
        ((nb068AlphaDummy059), (nb068AlphaDummy060 f)),
        ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy053))
        (synCphi (Class.cv (nb068AlphaDummy054))))
      (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
        (synCphi (Class.cv (nb068AlphaDummy056 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy048 f))).fv ∪
            ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy054) ≠ (nb068AlphaDummy061) from (by
                    unfold nb068AlphaDummy061;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 0))))
                (show (nb068AlphaDummy056 f) ≠ (nb068AlphaDummy063 f) from (by
                    unfold nb068AlphaDummy063;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy054) ≠ (nb068AlphaDummy062) from
                    (by
                      unfold nb068AlphaDummy062;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 1))))
                  (show (nb068AlphaDummy056 f) ≠ (nb068AlphaDummy064 f) from (by
                      unfold nb068AlphaDummy064;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy054))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy056 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy068) from
                                    (by
                                      unfold nb068AlphaDummy068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0056)
                                              1)))) (show
                                    (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy071 f) from
                                    (by
                                      unfold nb068AlphaDummy071;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0057 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy061) ≠ (nb068AlphaDummy067) from (by
                                        unfold nb068AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0056)
                                                0)))) (show (nb068AlphaDummy063 f) ≠
                                        (nb068AlphaDummy070 f) from (by
                                        unfold nb068AlphaDummy070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0057 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from
                                        (by
                                          unfold nb068AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0054)
                                                  0)))) (show (nb068AlphaDummy063 f) ≠
        (nb068AlphaDummy066 f) from (by
                                          unfold nb068AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0055 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb068AlphaDummy069), (nb068AlphaDummy072 f)),
                                      ((nb068AlphaDummy068), (nb068AlphaDummy071 f)),
                                      ((nb068AlphaDummy067), (nb068AlphaDummy070 f)),
                                      ((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
                                      ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
                                      ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
                                      ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                                      ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                                      ((nb068AlphaDummy059), (nb068AlphaDummy060 f)),
                                      ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0034 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from (by
                              unfold nb068AlphaDummy065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                          (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from (by
                              unfold nb068AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
                          ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
                          ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
                          ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                          ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                          ((nb068AlphaDummy059), (nb068AlphaDummy060 f)),
                          ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from (by
                            unfold nb068AlphaDummy065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                        (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from (by
                            unfold nb068AlphaDummy066;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from (by
                              unfold nb068AlphaDummy065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                          (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from (by
                              unfold nb068AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
                          ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
                          ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
                          ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                          ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                          ((nb068AlphaDummy059), (nb068AlphaDummy060 f)),
                          ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part024`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0036`. -/
@[expose]
noncomputable def nb068SplitAlpha0036 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy069), (nb068AlphaDummy072 f)),
        ((nb068AlphaDummy068), (nb068AlphaDummy071 f)),
        ((nb068AlphaDummy067), (nb068AlphaDummy070 f)),
        ((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
        ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
        ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
        ((nb068AlphaDummy087), (nb068AlphaDummy088 f)),
        ((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
        ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
        ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
        ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
        ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy067))
            (synCun (Class.cv (nb068AlphaDummy068)) (Class.cv (nb068AlphaDummy069))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy071 f))
            (Class.cv (nb068AlphaDummy072 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy070 f))
            (synCun (Class.cv (nb068AlphaDummy071 f))
              (Class.cv (nb068AlphaDummy072 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy075) from (by
                              unfold nb068AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy076 f) from (by
                              unfold nb068AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy073) from (by
                                unfold nb068AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy074 f) from (by
                                unfold nb068AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy069), (nb068AlphaDummy072 f)),
          ((nb068AlphaDummy068), (nb068AlphaDummy071 f)),
          ((nb068AlphaDummy067), (nb068AlphaDummy070 f)),
          ((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
          ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
          ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
          ((nb068AlphaDummy087), (nb068AlphaDummy088 f)),
          ((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
          ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
          ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
          ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
          ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy079) from (by
                                unfold nb068AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy080 f) from (by
                                unfold nb068AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy079) from (by
                                unfold nb068AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy080 f) from (by
                                unfold nb068AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy068) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068AlphaDummy071 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy061))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy063 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy081) from (by
                                unfold nb068AlphaDummy081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy082 f) from (by
                                unfold nb068AlphaDummy082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy081) from (by
                                unfold nb068AlphaDummy081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy082 f) from (by
                                unfold nb068AlphaDummy082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy069) ≠ (nb068AlphaDummy077) from (by
                                  unfold nb068AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068AlphaDummy072 f) ≠ (nb068AlphaDummy078 f) from
                                (by
                                  unfold nb068AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0037`. -/
@[expose]
noncomputable def nb068SplitAlpha0037 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
        ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
        ((nb068AlphaDummy087), (nb068AlphaDummy088 f)),
        ((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
        ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
        ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
        ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
        ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy061))
          (Class.cv (nb068AlphaDummy054))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy062))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy061)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy061)) (synC1c))
              (Class.cv (nb068AlphaDummy061))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy063 f))
          (Class.cv (nb068AlphaDummy056 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy064 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy063 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy063 f)) (synC1c))
              (Class.cv (nb068AlphaDummy063 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy054) ≠ (nb068AlphaDummy061) from (by
              unfold nb068AlphaDummy061;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 0))))
          (show (nb068AlphaDummy056 f) ≠ (nb068AlphaDummy063 f) from (by
              unfold nb068AlphaDummy063;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy054) ≠ (nb068AlphaDummy062) from (by
                unfold nb068AlphaDummy062;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 1))))
            (show (nb068AlphaDummy056 f) ≠ (nb068AlphaDummy064 f) from (by
                unfold nb068AlphaDummy064;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy054) ≠ (nb068AlphaDummy087) from (by
                  unfold nb068AlphaDummy087;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0082) 0))))
              (show (nb068AlphaDummy056 f) ≠ (nb068AlphaDummy088 f) from (by
                  unfold nb068AlphaDummy088;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0083 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy054) ≠ (nb068AlphaDummy085) from (by
                    unfold nb068AlphaDummy085;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0080) 0))))
                (show (nb068AlphaDummy056 f) ≠ (nb068AlphaDummy086 f) from (by
                    unfold nb068AlphaDummy086;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0081 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy054))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy056 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy068) from (by
                                  unfold nb068AlphaDummy068;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0056) 1))))
                              (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy071 f) from
                                (by
                                  unfold nb068AlphaDummy071;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0057 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy067) from (by
                                    unfold nb068AlphaDummy067;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0056) 0)))) (show
                                  (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy070 f) from (by
                                    unfold nb068AlphaDummy070;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0057 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from
                                    (by
                                      unfold nb068AlphaDummy065;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0054)
                                              0)))) (show
                                    (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from
                                    (by
                                      unfold nb068AlphaDummy066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0055 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy069), (nb068AlphaDummy072 f)),
                                  ((nb068AlphaDummy068), (nb068AlphaDummy071 f)),
                                  ((nb068AlphaDummy067), (nb068AlphaDummy070 f)),
                                  ((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
                                  ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
                                  ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
                                  ((nb068AlphaDummy087), (nb068AlphaDummy088 f)),
                                  ((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
                                  ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                                  ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                                  ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
                                  ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                                  ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                  ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                  ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0036 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from (by
                          unfold nb068AlphaDummy065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                      (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from (by
                          unfold nb068AlphaDummy066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
                      ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
                      ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
                      ((nb068AlphaDummy087), (nb068AlphaDummy088 f)),
                      ((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
                      ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                      ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                      ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
                      ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from
                      (by
                        unfold nb068AlphaDummy065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                    (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from (by
                        unfold nb068AlphaDummy066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy061) ≠ (nb068AlphaDummy065) from (by
                          unfold nb068AlphaDummy065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                      (show (nb068AlphaDummy063 f) ≠ (nb068AlphaDummy066 f) from (by
                          unfold nb068AlphaDummy066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy065), (nb068AlphaDummy066 f)),
                      ((nb068AlphaDummy061), (nb068AlphaDummy063 f)),
                      ((nb068AlphaDummy062), (nb068AlphaDummy064 f)),
                      ((nb068AlphaDummy087), (nb068AlphaDummy088 f)),
                      ((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
                      ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                      ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                      ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
                      ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0038`. -/
@[expose]
noncomputable def nb068SplitAlpha0038 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
        ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy083))
          (Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy083))
            (Class.cab (nb068AlphaDummy053)
              (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy053))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy084 f))
          (Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy084 f))
            (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy054) from
                    (by
                      unfold nb068AlphaDummy054;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
                  (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy056 f) from (by
                      unfold nb068AlphaDummy056;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy053) from
                      (by
                        unfold nb068AlphaDummy053;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))))
                    (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy055 f) from (by
                        unfold nb068AlphaDummy055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0076 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy083) from (by
                          unfold nb068AlphaDummy083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0078) 0))))
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy084 f) from (by
                          unfold nb068AlphaDummy084;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0079 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy057) from (by
                            unfold nb068AlphaDummy057;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0075) 0))))
                        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy058 f) from (by
                            unfold nb068AlphaDummy058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0077 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
                      ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy048 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0037 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0037 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
                          ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                          ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                          ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
                          ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
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
                  (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy054) from
                      (by
                        unfold nb068AlphaDummy054;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
                    (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy056 f) from (by
                        unfold nb068AlphaDummy056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0076 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy053) from (by
                          unfold nb068AlphaDummy053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0074) 0))))
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy055 f) from (by
                          unfold nb068AlphaDummy055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0076 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy083) from (by
                            unfold nb068AlphaDummy083;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0078) 0))))
                        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy084 f) from (by
                            unfold nb068AlphaDummy084;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0079 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy057) from (by
                              unfold nb068AlphaDummy057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0075) 0))))
                          (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy058 f) from (by
                              unfold nb068AlphaDummy058;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0077 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy045))).fv ∪
                        ((Class.cv (nb068AlphaDummy046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy048 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0037 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0037 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy085), (nb068AlphaDummy086 f)),
                            ((nb068AlphaDummy054), (nb068AlphaDummy056 f)),
                            ((nb068AlphaDummy053), (nb068AlphaDummy055 f)),
                            ((nb068AlphaDummy083), (nb068AlphaDummy084 f)),
                            ((nb068AlphaDummy057), (nb068AlphaDummy058 f)),
                            ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                            ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                            ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0039`. -/
@[expose]
noncomputable def nb068SplitAlpha0039 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy105), (nb068AlphaDummy108 f)),
        ((nb068AlphaDummy104), (nb068AlphaDummy107 f)),
        ((nb068AlphaDummy103), (nb068AlphaDummy106 f)),
        ((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
        ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
        ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
        ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
        ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
        ((nb068AlphaDummy095), (nb068AlphaDummy096 f)),
        ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy103))
            (synCun (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy106 f))
            (synCun (Class.cv (nb068AlphaDummy107 f))
              (Class.cv (nb068AlphaDummy108 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy105), (nb068AlphaDummy108 f)),
          ((nb068AlphaDummy104), (nb068AlphaDummy107 f)),
          ((nb068AlphaDummy103), (nb068AlphaDummy106 f)),
          ((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
          ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
          ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
          ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
          ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
          ((nb068AlphaDummy095), (nb068AlphaDummy096 f)),
          ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy115) from (by
                                unfold nb068AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy116 f) from (by
                                unfold nb068AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy115) from (by
                                unfold nb068AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy116 f) from (by
                                unfold nb068AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy117) from (by
                                unfold nb068AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy118 f) from (by
                                unfold nb068AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy117) from (by
                                unfold nb068AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy118 f) from (by
                                unfold nb068AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part025`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0040`. -/
@[expose]
noncomputable def nb068SplitAlpha0040 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
        ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
        ((nb068AlphaDummy095), (nb068AlphaDummy096 f)),
        ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy089))
        (synCphi (Class.cv (nb068AlphaDummy090))))
      (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
        (synCphi (Class.cv (nb068AlphaDummy092 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy048 f))).fv ∪
            ((Class.cv (nb068AlphaDummy050 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy090) ≠ (nb068AlphaDummy097) from (by
                    unfold nb068AlphaDummy097;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 0))))
                (show (nb068AlphaDummy092 f) ≠ (nb068AlphaDummy099 f) from (by
                    unfold nb068AlphaDummy099;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy090) ≠ (nb068AlphaDummy098) from
                    (by
                      unfold nb068AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 1))))
                  (show (nb068AlphaDummy092 f) ≠ (nb068AlphaDummy100 f) from (by
                      unfold nb068AlphaDummy100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy090))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy092 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy104) from
                                    (by
                                      unfold nb068AlphaDummy104;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0094)
                                              1)))) (show
                                    (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy107 f) from
                                    (by
                                      unfold nb068AlphaDummy107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0095 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy097) ≠ (nb068AlphaDummy103) from (by
                                        unfold nb068AlphaDummy103;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0094)
                                                0)))) (show (nb068AlphaDummy099 f) ≠
                                        (nb068AlphaDummy106 f) from (by
                                        unfold nb068AlphaDummy106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0095 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from
                                        (by
                                          unfold nb068AlphaDummy101;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0092)
                                                  0)))) (show (nb068AlphaDummy099 f) ≠
        (nb068AlphaDummy102 f) from (by
                                          unfold nb068AlphaDummy102;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb068AlphaDummy105), (nb068AlphaDummy108 f)),
                                      ((nb068AlphaDummy104), (nb068AlphaDummy107 f)),
                                      ((nb068AlphaDummy103), (nb068AlphaDummy106 f)),
                                      ((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
                                      ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
                                      ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
                                      ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                                      ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                                      ((nb068AlphaDummy095), (nb068AlphaDummy096 f)),
                                      ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
                                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0039 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from (by
                              unfold nb068AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                          (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from (by
                              unfold nb068AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
                          ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
                          ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
                          ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                          ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                          ((nb068AlphaDummy095), (nb068AlphaDummy096 f)),
                          ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
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
                        (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from (by
                            unfold nb068AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                        (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from (by
                            unfold nb068AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from (by
                              unfold nb068AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                          (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from (by
                              unfold nb068AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
                          ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
                          ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
                          ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                          ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                          ((nb068AlphaDummy095), (nb068AlphaDummy096 f)),
                          ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
                          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0041`. -/
@[expose]
noncomputable def nb068SplitAlpha0041 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy105), (nb068AlphaDummy108 f)),
        ((nb068AlphaDummy104), (nb068AlphaDummy107 f)),
        ((nb068AlphaDummy103), (nb068AlphaDummy106 f)),
        ((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
        ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
        ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
        ((nb068AlphaDummy123), (nb068AlphaDummy124 f)),
        ((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
        ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
        ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
        ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
        ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy103))
            (synCun (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy106 f))
            (synCun (Class.cv (nb068AlphaDummy107 f))
              (Class.cv (nb068AlphaDummy108 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy111) from (by
                              unfold nb068AlphaDummy111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy112 f) from (by
                              unfold nb068AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy109) from (by
                                unfold nb068AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy110 f) from (by
                                unfold nb068AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy105), (nb068AlphaDummy108 f)),
          ((nb068AlphaDummy104), (nb068AlphaDummy107 f)),
          ((nb068AlphaDummy103), (nb068AlphaDummy106 f)),
          ((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
          ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
          ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
          ((nb068AlphaDummy123), (nb068AlphaDummy124 f)),
          ((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
          ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
          ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
          ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
          ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy115) from (by
                                unfold nb068AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy116 f) from (by
                                unfold nb068AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy115) from (by
                                unfold nb068AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy116 f) from (by
                                unfold nb068AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy104) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068AlphaDummy107 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy117) from (by
                                unfold nb068AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy118 f) from (by
                                unfold nb068AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy117) from (by
                                unfold nb068AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy118 f) from (by
                                unfold nb068AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy105) ≠ (nb068AlphaDummy113) from (by
                                  unfold nb068AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068AlphaDummy108 f) ≠ (nb068AlphaDummy114 f) from
                                (by
                                  unfold nb068AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0042`. -/
@[expose]
noncomputable def nb068SplitAlpha0042 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
        ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
        ((nb068AlphaDummy123), (nb068AlphaDummy124 f)),
        ((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
        ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
        ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
        ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
        ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy097))
          (Class.cv (nb068AlphaDummy090))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy098))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy097)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy097)) (synC1c))
              (Class.cv (nb068AlphaDummy097))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy099 f))
          (Class.cv (nb068AlphaDummy092 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy100 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy099 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy099 f)) (synC1c))
              (Class.cv (nb068AlphaDummy099 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy090) ≠ (nb068AlphaDummy097) from (by
              unfold nb068AlphaDummy097;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 0))))
          (show (nb068AlphaDummy092 f) ≠ (nb068AlphaDummy099 f) from (by
              unfold nb068AlphaDummy099;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy090) ≠ (nb068AlphaDummy098) from (by
                unfold nb068AlphaDummy098;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 1))))
            (show (nb068AlphaDummy092 f) ≠ (nb068AlphaDummy100 f) from (by
                unfold nb068AlphaDummy100;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy090) ≠ (nb068AlphaDummy123) from (by
                  unfold nb068AlphaDummy123;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0120) 0))))
              (show (nb068AlphaDummy092 f) ≠ (nb068AlphaDummy124 f) from (by
                  unfold nb068AlphaDummy124;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0121 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy090) ≠ (nb068AlphaDummy121) from (by
                    unfold nb068AlphaDummy121;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0118) 0))))
                (show (nb068AlphaDummy092 f) ≠ (nb068AlphaDummy122 f) from (by
                    unfold nb068AlphaDummy122;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0119 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy090))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy092 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy104) from (by
                                  unfold nb068AlphaDummy104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0094) 1))))
                              (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy107 f) from
                                (by
                                  unfold nb068AlphaDummy107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0095 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy103) from (by
                                    unfold nb068AlphaDummy103;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0094) 0)))) (show
                                  (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy106 f) from (by
                                    unfold nb068AlphaDummy106;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0095 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from
                                    (by
                                      unfold nb068AlphaDummy101;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0092)
                                              0)))) (show
                                    (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from
                                    (by
                                      unfold nb068AlphaDummy102;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy105), (nb068AlphaDummy108 f)),
                                  ((nb068AlphaDummy104), (nb068AlphaDummy107 f)),
                                  ((nb068AlphaDummy103), (nb068AlphaDummy106 f)),
                                  ((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
                                  ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
                                  ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
                                  ((nb068AlphaDummy123), (nb068AlphaDummy124 f)),
                                  ((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
                                  ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                                  ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                                  ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
                                  ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
                                  ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                                  ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                  ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                  ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0041 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from (by
                          unfold nb068AlphaDummy101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                      (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from (by
                          unfold nb068AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
                      ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
                      ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
                      ((nb068AlphaDummy123), (nb068AlphaDummy124 f)),
                      ((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
                      ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                      ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                      ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
                      ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from
                      (by
                        unfold nb068AlphaDummy101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                    (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from (by
                        unfold nb068AlphaDummy102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy097) ≠ (nb068AlphaDummy101) from (by
                          unfold nb068AlphaDummy101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                      (show (nb068AlphaDummy099 f) ≠ (nb068AlphaDummy102 f) from (by
                          unfold nb068AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy101), (nb068AlphaDummy102 f)),
                      ((nb068AlphaDummy097), (nb068AlphaDummy099 f)),
                      ((nb068AlphaDummy098), (nb068AlphaDummy100 f)),
                      ((nb068AlphaDummy123), (nb068AlphaDummy124 f)),
                      ((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
                      ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                      ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                      ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
                      ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0043`. -/
@[expose]
noncomputable def nb068SplitAlpha0043 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
        ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy119))
          (Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy119))
            (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy120 f))
          (Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy120 f))
            (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy090) from
                    (by
                      unfold nb068AlphaDummy090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
                  (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy092 f) from (by
                      unfold nb068AlphaDummy092;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy089) from
                      (by
                        unfold nb068AlphaDummy089;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))))
                    (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy091 f) from (by
                        unfold nb068AlphaDummy091;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0114 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy119) from (by
                          unfold nb068AlphaDummy119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0116) 0))))
                      (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy120 f) from (by
                          unfold nb068AlphaDummy120;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0117 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy093) from (by
                            unfold nb068AlphaDummy093;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0113) 0))))
                        (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy094 f) from (by
                            unfold nb068AlphaDummy094;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0115 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
                      ((Class.cv (nb068AlphaDummy047))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy048 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy050 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0042 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0042 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
                          ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                          ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                          ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
                          ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
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
                  (TAlphaVar.there (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy090) from
                      (by
                        unfold nb068AlphaDummy090;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
                    (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy092 f) from (by
                        unfold nb068AlphaDummy092;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0114 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy089) from (by
                          unfold nb068AlphaDummy089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0112) 0))))
                      (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy091 f) from (by
                          unfold nb068AlphaDummy091;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0114 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy119) from (by
                            unfold nb068AlphaDummy119;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0116) 0))))
                        (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy120 f) from (by
                            unfold nb068AlphaDummy120;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0117 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy093) from (by
                              unfold nb068AlphaDummy093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0113) 0))))
                          (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy094 f) from (by
                              unfold nb068AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0115 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy045))).fv ∪
                        ((Class.cv (nb068AlphaDummy047))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy048 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy050 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0042 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0042 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy121), (nb068AlphaDummy122 f)),
                            ((nb068AlphaDummy090), (nb068AlphaDummy092 f)),
                            ((nb068AlphaDummy089), (nb068AlphaDummy091 f)),
                            ((nb068AlphaDummy119), (nb068AlphaDummy120 f)),
                            ((nb068AlphaDummy093), (nb068AlphaDummy094 f)),
                            ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                            ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                            ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                            ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part026`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0044`. -/
@[expose]
noncomputable def nb068SplitAlpha0044 (x : Var) (y : Var) (f : Var) :
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
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
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
          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0045`. -/
@[expose]
noncomputable def nb068SplitAlpha0045 (x : Var) (y : Var) (f : Var) :
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
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy139))
          (Class.cv (nb068AlphaDummy132))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy140))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
              (Class.cv (nb068AlphaDummy139))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy141 f))
          (Class.cv (nb068AlphaDummy134 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
              (Class.cv (nb068AlphaDummy141 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
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
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
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
                                  ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                                  ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                  ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                  ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0044 x y f))))))))
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
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
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
                      ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                      ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                      ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                      ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0046`. -/
@[expose]
noncomputable def nb068SplitAlpha0046 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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
          ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
          ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0047`. -/
@[expose]
noncomputable def nb068SplitAlpha0047 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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
      (Wff.classEq (Class.cv (nb068AlphaDummy140))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
          (Class.cv (nb068AlphaDummy139))))
      (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
          (Class.cv (nb068AlphaDummy141 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                              unfold nb068AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                          (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from (by
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
                                      (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                            (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                unfold nb068AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                                  unfold nb068AlphaDummy143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                (by
                                  unfold nb068AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                              ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                              ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                              ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                              ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                              ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                              ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                              ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                              ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                              ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                              ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                              ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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
                        (TAlphaWff.neg (nb068SplitAlpha0046 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                      unfold nb068AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                      unfold nb068AlphaDummy144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                  ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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
              (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                    unfold nb068AlphaDummy143;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                    unfold nb068AlphaDummy144;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                  ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part027`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0048`. -/
@[expose]
noncomputable def nb068SplitAlpha0048 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy161))
          (Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy161))
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
          (Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                    (by
                      unfold nb068AlphaDummy132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                  (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                      unfold nb068AlphaDummy134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from
                      (by
                        unfold nb068AlphaDummy131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                        unfold nb068AlphaDummy133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                          unfold nb068AlphaDummy161;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                          unfold nb068AlphaDummy162;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                            unfold nb068AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                            unfold nb068AlphaDummy136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
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
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0047 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
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
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0047 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                      (by
                        unfold nb068AlphaDummy132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                        unfold nb068AlphaDummy134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from (by
                          unfold nb068AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                          unfold nb068AlphaDummy133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                            unfold nb068AlphaDummy161;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                            unfold nb068AlphaDummy162;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                              unfold nb068AlphaDummy135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                          (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                              unfold nb068AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy125))).fv ∪
                        ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
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
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0047 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
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
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0047 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                            ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                            ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                            ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                            ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0049`. -/
@[expose]
noncomputable def nb068SplitAlpha0049 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
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
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
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
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0050`. -/
@[expose]
noncomputable def nb068SplitAlpha0050 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy175))
          (Class.cv (nb068AlphaDummy168))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy176))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
              (Class.cv (nb068AlphaDummy175))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy177 f))
          (Class.cv (nb068AlphaDummy170 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
              (Class.cv (nb068AlphaDummy177 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
              unfold nb068AlphaDummy175;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
          (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy177 f) from (by
              unfold nb068AlphaDummy177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
                unfold nb068AlphaDummy176;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
            (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy178 f) from (by
                unfold nb068AlphaDummy178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                                  unfold nb068AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from
                                (by
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
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                    unfold nb068AlphaDummy184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                                    (by
                                      unfold nb068AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                    (by
                                      unfold nb068AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                                  ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                                  ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                                  ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                                  ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                                  ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                                  ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                                  ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0049 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
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
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
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
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0051`. -/
@[expose]
noncomputable def nb068SplitAlpha0051 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
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
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
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
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
