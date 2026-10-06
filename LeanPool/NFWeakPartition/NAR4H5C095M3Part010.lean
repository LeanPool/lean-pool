/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part009

/-! NF weak partition development: NAR4H5C095M3Part010. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0003`. -/
@[expose]
noncomputable def nb095SplitAlpha0003 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
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
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095AlphaDummy087 D R S_cls E))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy088 f))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy058 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                            (nb095AlphaDummy063 D R S_cls E) from (by
                            unfold nb095AlphaDummy063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy065 f) from (by
                            unfold nb095AlphaDummy065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0049 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                              (nb095AlphaDummy064 D R S_cls E) from (by
                              unfold nb095AlphaDummy064;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy066 f) from (by
                              unfold nb095AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0049 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                                (nb095AlphaDummy089 D R S_cls E) from (by
                                unfold nb095AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0078 D R S_cls E) 0))))
                            (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy090 f) from (by
                                unfold nb095AlphaDummy090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0079 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                                  (nb095AlphaDummy087 D R S_cls E) from (by
                                  unfold nb095AlphaDummy087;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0076 D R S_cls E) 0))))
                              (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy088 f) from
                                (by
                                  unfold nb095AlphaDummy088;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0077 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy058 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy070 D R S_cls E) from (by
          unfold nb095AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls E)
                  1)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy073 f) from (by
          unfold nb095AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy069 D R S_cls E) from (by
          unfold nb095AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy072 f) from (by
          unfold nb095AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy067 D R S_cls E) from (by
          unfold nb095AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0050 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from (by
          unfold nb095AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0051 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy089 D R S_cls E), (nb095AlphaDummy090 f)),
        ((nb095AlphaDummy087 D R S_cls E), (nb095AlphaDummy088 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy089 D R S_cls E), (nb095AlphaDummy090 f)),
        ((nb095AlphaDummy087 D R S_cls E), (nb095AlphaDummy088 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy070 D
        R S_cls E) ≠ (nb095AlphaDummy081 D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy081
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071 D
        R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071 D
        R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy063 D R S_cls E) ≠
                                      (nb095AlphaDummy067 D R S_cls E) from (by
                                      unfold nb095AlphaDummy067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                    (by
                                      unfold nb095AlphaDummy068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy067 D R S_cls E),
                                    (nb095AlphaDummy068 f)),
                                  ((nb095AlphaDummy063 D R S_cls E),
                                    (nb095AlphaDummy065 f)),
                                  ((nb095AlphaDummy064 D R S_cls E),
                                    (nb095AlphaDummy066 f)),
                                  ((nb095AlphaDummy089 D R S_cls E),
                                    (nb095AlphaDummy090 f)),
                                  ((nb095AlphaDummy087 D R S_cls E),
                                    (nb095AlphaDummy088 f)),
                                  ((nb095AlphaDummy056 D R S_cls E),
                                    (nb095AlphaDummy058 f)),
                                  ((nb095AlphaDummy055 D R S_cls E),
                                    (nb095AlphaDummy057 f)),
                                  ((nb095AlphaDummy085 D R S_cls E),
                                    (nb095AlphaDummy086 f)),
                                  ((nb095AlphaDummy059 D R S_cls E),
                                    (nb095AlphaDummy060 f)),
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
                                  (nb095AlphaDummy063 D R S_cls E) ≠
                                    (nb095AlphaDummy067 D R S_cls E) from (by
                                    unfold nb095AlphaDummy067;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from (by
                                    unfold nb095AlphaDummy068;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0051 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy063 D R S_cls E) ≠
                                      (nb095AlphaDummy067 D R S_cls E) from (by
                                      unfold nb095AlphaDummy067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                    (by
                                      unfold nb095AlphaDummy068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy067 D R S_cls E),
                                    (nb095AlphaDummy068 f)),
                                  ((nb095AlphaDummy063 D R S_cls E),
                                    (nb095AlphaDummy065 f)),
                                  ((nb095AlphaDummy064 D R S_cls E),
                                    (nb095AlphaDummy066 f)),
                                  ((nb095AlphaDummy089 D R S_cls E),
                                    (nb095AlphaDummy090 f)),
                                  ((nb095AlphaDummy087 D R S_cls E),
                                    (nb095AlphaDummy088 f)),
                                  ((nb095AlphaDummy056 D R S_cls E),
                                    (nb095AlphaDummy058 f)),
                                  ((nb095AlphaDummy055 D R S_cls E),
                                    (nb095AlphaDummy057 f)),
                                  ((nb095AlphaDummy085 D R S_cls E),
                                    (nb095AlphaDummy086 f)),
                                  ((nb095AlphaDummy059 D R S_cls E),
                                    (nb095AlphaDummy060 f)),
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
                      (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                            (nb095AlphaDummy063 D R S_cls E) from (by
                            unfold nb095AlphaDummy063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy065 f) from (by
                            unfold nb095AlphaDummy065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0049 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                              (nb095AlphaDummy064 D R S_cls E) from (by
                              unfold nb095AlphaDummy064;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy066 f) from (by
                              unfold nb095AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0049 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                                (nb095AlphaDummy089 D R S_cls E) from (by
                                unfold nb095AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0078 D R S_cls E) 0))))
                            (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy090 f) from (by
                                unfold nb095AlphaDummy090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0079 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                                  (nb095AlphaDummy087 D R S_cls E) from (by
                                  unfold nb095AlphaDummy087;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0076 D R S_cls E) 0))))
                              (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy088 f) from
                                (by
                                  unfold nb095AlphaDummy088;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0077 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy058 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy070 D R S_cls E) from (by
          unfold nb095AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls E)
                  1)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy073 f) from (by
          unfold nb095AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy069 D R S_cls E) from (by
          unfold nb095AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy072 f) from (by
          unfold nb095AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy067 D R S_cls E) from (by
          unfold nb095AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0050 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from (by
          unfold nb095AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0051 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy089 D R S_cls E), (nb095AlphaDummy090 f)),
        ((nb095AlphaDummy087 D R S_cls E), (nb095AlphaDummy088 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy089 D R S_cls E), (nb095AlphaDummy090 f)),
        ((nb095AlphaDummy087 D R S_cls E), (nb095AlphaDummy088 f)),
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
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy070 D
        R S_cls E) ≠ (nb095AlphaDummy081 D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy081
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071 D
        R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071 D
        R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy063 D R S_cls E) ≠
                                      (nb095AlphaDummy067 D R S_cls E) from (by
                                      unfold nb095AlphaDummy067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                    (by
                                      unfold nb095AlphaDummy068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy067 D R S_cls E),
                                    (nb095AlphaDummy068 f)),
                                  ((nb095AlphaDummy063 D R S_cls E),
                                    (nb095AlphaDummy065 f)),
                                  ((nb095AlphaDummy064 D R S_cls E),
                                    (nb095AlphaDummy066 f)),
                                  ((nb095AlphaDummy089 D R S_cls E),
                                    (nb095AlphaDummy090 f)),
                                  ((nb095AlphaDummy087 D R S_cls E),
                                    (nb095AlphaDummy088 f)),
                                  ((nb095AlphaDummy056 D R S_cls E),
                                    (nb095AlphaDummy058 f)),
                                  ((nb095AlphaDummy055 D R S_cls E),
                                    (nb095AlphaDummy057 f)),
                                  ((nb095AlphaDummy085 D R S_cls E),
                                    (nb095AlphaDummy086 f)),
                                  ((nb095AlphaDummy059 D R S_cls E),
                                    (nb095AlphaDummy060 f)),
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
                                  (nb095AlphaDummy063 D R S_cls E) ≠
                                    (nb095AlphaDummy067 D R S_cls E) from (by
                                    unfold nb095AlphaDummy067;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from (by
                                    unfold nb095AlphaDummy068;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0051 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy063 D R S_cls E) ≠
                                      (nb095AlphaDummy067 D R S_cls E) from (by
                                      unfold nb095AlphaDummy067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                    (by
                                      unfold nb095AlphaDummy068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy067 D R S_cls E),
                                    (nb095AlphaDummy068 f)),
                                  ((nb095AlphaDummy063 D R S_cls E),
                                    (nb095AlphaDummy065 f)),
                                  ((nb095AlphaDummy064 D R S_cls E),
                                    (nb095AlphaDummy066 f)),
                                  ((nb095AlphaDummy089 D R S_cls E),
                                    (nb095AlphaDummy090 f)),
                                  ((nb095AlphaDummy087 D R S_cls E),
                                    (nb095AlphaDummy088 f)),
                                  ((nb095AlphaDummy056 D R S_cls E),
                                    (nb095AlphaDummy058 f)),
                                  ((nb095AlphaDummy055 D R S_cls E),
                                    (nb095AlphaDummy057 f)),
                                  ((nb095AlphaDummy085 D R S_cls E),
                                    (nb095AlphaDummy086 f)),
                                  ((nb095AlphaDummy059 D R S_cls E),
                                    (nb095AlphaDummy060 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0004`. -/
@[expose]
noncomputable def nb095SplitAlpha0004 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
          (Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
            (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
          (Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
            (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCphi (Class.cv (nb095AlphaDummy100 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                      (nb095AlphaDummy098 D R S_cls E) from (by
                      unfold nb095AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                  (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                      unfold nb095AlphaDummy100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy097 D R S_cls E) from (by
                        unfold nb095AlphaDummy097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                        unfold nb095AlphaDummy099;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy103 D R S_cls E) from (by
                          unfold nb095AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                          unfold nb095AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy101 D R S_cls E) from (by
                            unfold nb095AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                            unfold nb095AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy105 D R S_cls E) from (by
                              unfold nb095AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                              unfold nb095AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy106 D R S_cls E) from (by
                                unfold nb095AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                                unfold nb095AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
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
                                    (nb095AlphaDummy105 D R S_cls E) ≠
                                      (nb095AlphaDummy109 D R S_cls E) from (by
                                      unfold nb095AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                    (by
                                      unfold nb095AlphaDummy110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy098 D R S_cls E) from (by
                        unfold nb095AlphaDummy098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                        unfold nb095AlphaDummy100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy097 D R S_cls E) from (by
                          unfold nb095AlphaDummy097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                          unfold nb095AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy103 D R S_cls E) from (by
                            unfold nb095AlphaDummy103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                            unfold nb095AlphaDummy104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                              (nb095AlphaDummy101 D R S_cls E) from (by
                              unfold nb095AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                              unfold nb095AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                            (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy105 D R S_cls E) from (by
                                unfold nb095AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 0))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                                unfold nb095AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                  (nb095AlphaDummy106 D R S_cls E) from (by
                                  unfold nb095AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0090 D R S_cls E) 1))))
                              (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from
                                (by
                                  unfold nb095AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy100 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
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
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0005`. -/
@[expose]
noncomputable def nb095SplitAlpha0005 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
        ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy131 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy131 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy132 f))
          (synCphi (Class.cv (nb095AlphaDummy100 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy132 f))
            (synCphi (Class.cv (nb095AlphaDummy100 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                      (nb095AlphaDummy105 D R S_cls E) from (by
                      unfold nb095AlphaDummy105;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 0))))
                  (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                      unfold nb095AlphaDummy107;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                  (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                        (nb095AlphaDummy106 D R S_cls E) from (by
                        unfold nb095AlphaDummy106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 1))))
                    (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                        unfold nb095AlphaDummy108;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0091 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy098 D R S_cls E) ≠
                          (nb095AlphaDummy131 D R S_cls E) from (by
                          unfold nb095AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0120 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy132 f) from (by
                          unfold nb095AlphaDummy132;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                            (nb095AlphaDummy129 D R S_cls E) from (by
                            unfold nb095AlphaDummy129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0118 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy130 f) from (by
                            unfold nb095AlphaDummy130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0119 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy112 D R S_cls E) from (by
                                        unfold nb095AlphaDummy112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0094 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from
                                      (by
                                        unfold nb095AlphaDummy115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0095 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy111 D R S_cls E) from (by
                                          unfold nb095AlphaDummy111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0094 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy114 f) from (by
                                          unfold nb095AlphaDummy114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0095 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy113 D R S_cls E),
        (nb095AlphaDummy116 f)), ((nb095AlphaDummy112 D R S_cls E),
        (nb095AlphaDummy115 f)), ((nb095AlphaDummy111 D R S_cls E),
        (nb095AlphaDummy114 f)), ((nb095AlphaDummy109 D R S_cls E),
        (nb095AlphaDummy110 f)), ((nb095AlphaDummy105 D R S_cls E),
        (nb095AlphaDummy107 f)), ((nb095AlphaDummy106 D R S_cls E),
        (nb095AlphaDummy108 f)), ((nb095AlphaDummy131 D R S_cls E),
        (nb095AlphaDummy132 f)), ((nb095AlphaDummy129 D R S_cls E),
        (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
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
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy113 D R S_cls E),
        (nb095AlphaDummy116 f)), ((nb095AlphaDummy112 D R S_cls E),
        (nb095AlphaDummy115 f)), ((nb095AlphaDummy111 D R S_cls E),
        (nb095AlphaDummy114 f)), ((nb095AlphaDummy109 D R S_cls E),
        (nb095AlphaDummy110 f)), ((nb095AlphaDummy105 D R S_cls E),
        (nb095AlphaDummy107 f)), ((nb095AlphaDummy106 D R S_cls E),
        (nb095AlphaDummy108 f)), ((nb095AlphaDummy131 D R S_cls E),
        (nb095AlphaDummy132 f)), ((nb095AlphaDummy129 D R S_cls E),
        (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
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
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123 D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy123 D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy105 D R S_cls E) ≠
                                (nb095AlphaDummy109 D R S_cls E) from (by
                                unfold nb095AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
                                unfold nb095AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
                            ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
                            ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
                            ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
                            ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
                            ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
                            ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
                            ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
                            ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
                            ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                            ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                            ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                            ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                            ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                            ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                            ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                            ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
                            ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
                              (nb095AlphaDummy109 D R S_cls E) from (by
                              unfold nb095AlphaDummy109;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0092 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
                              unfold nb095AlphaDummy110;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy105 D R S_cls E) ≠
                                (nb095AlphaDummy109 D R S_cls E) from (by
                                unfold nb095AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
                                unfold nb095AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
                            ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
                            ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
                            ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
                            ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
                            ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
                            ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
                            ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
                            ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
                            ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                            ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                            ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                            ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                            ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                            ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                            ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                            ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
                            ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                        (nb095AlphaDummy105 D R S_cls E) from (by
                        unfold nb095AlphaDummy105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 0))))
                    (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                        unfold nb095AlphaDummy107;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0091 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy098 D R S_cls E) ≠
                          (nb095AlphaDummy106 D R S_cls E) from (by
                          unfold nb095AlphaDummy106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                  1))))
                      (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                          unfold nb095AlphaDummy108;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                            (nb095AlphaDummy131 D R S_cls E) from (by
                            unfold nb095AlphaDummy131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0120 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy132 f) from (by
                            unfold nb095AlphaDummy132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy129 D R S_cls E) from (by
                              unfold nb095AlphaDummy129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0118 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy130 f) from (by
                              unfold nb095AlphaDummy130;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0119 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
                                          unfold nb095AlphaDummy112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0094 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy115 f) from (by
                                          unfold nb095AlphaDummy115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0095 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy113 D R S_cls E),
        (nb095AlphaDummy116 f)), ((nb095AlphaDummy112 D R S_cls E),
        (nb095AlphaDummy115 f)), ((nb095AlphaDummy111 D R S_cls E),
        (nb095AlphaDummy114 f)), ((nb095AlphaDummy109 D R S_cls E),
        (nb095AlphaDummy110 f)), ((nb095AlphaDummy105 D R S_cls E),
        (nb095AlphaDummy107 f)), ((nb095AlphaDummy106 D R S_cls E),
        (nb095AlphaDummy108 f)), ((nb095AlphaDummy131 D R S_cls E),
        (nb095AlphaDummy132 f)), ((nb095AlphaDummy129 D R S_cls E),
        (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
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
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
        ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R S_cls
        E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123 D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy105 D R S_cls E) ≠
                                  (nb095AlphaDummy109 D R S_cls E) from (by
                                  unfold nb095AlphaDummy109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0092 D R S_cls E) 0))))
                              (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                (by
                                  unfold nb095AlphaDummy110;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
                              ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
                              ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
                              ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
                              ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
                              ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
                              ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
                              ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
                              ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
                              ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                              ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                              ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                              ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                              ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                              ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                              ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                              ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
                              ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy105 D R S_cls E) ≠
                                (nb095AlphaDummy109 D R S_cls E) from (by
                                unfold nb095AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
                                unfold nb095AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy105 D R S_cls E) ≠
                                  (nb095AlphaDummy109 D R S_cls E) from (by
                                  unfold nb095AlphaDummy109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0092 D R S_cls E) 0))))
                              (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                (by
                                  unfold nb095AlphaDummy110;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
                              ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
                              ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
                              ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
                              ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
                              ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
                              ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
                              ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
                              ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
                              ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                              ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                              ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                              ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                              ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                              ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                              ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                              ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
                              ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
