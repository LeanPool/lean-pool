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

@[expose]
noncomputable def nb095_split_alpha_0003 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095_alpha_dummy_087 D R S_cls E))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_056 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_088 f))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_058 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                            (nb095_alpha_dummy_063 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_065 f) from (by
                            unfold nb095_alpha_dummy_065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0049 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                              (nb095_alpha_dummy_064 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_064;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_066 f) from (by
                              unfold nb095_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0049 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                                (nb095_alpha_dummy_089 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0078 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_090 f) from (by
                                unfold nb095_alpha_dummy_090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0079 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                                  (nb095_alpha_dummy_087 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_087;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0076 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_088 f) from
                                (by
                                  unfold nb095_alpha_dummy_088;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0077 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_058 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_070 D R S_cls E) from (by
          unfold nb095_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_073 f) from (by
          unfold nb095_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_069 D R S_cls E) from (by
          unfold nb095_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_072 f) from (by
          unfold nb095_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_067 D R S_cls E) from (by
          unfold nb095_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0050 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from (by
          unfold nb095_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0051 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_071 D R S_cls E), (nb095_alpha_dummy_074 f)),
        ((nb095_alpha_dummy_070 D R S_cls E), (nb095_alpha_dummy_073 f)),
        ((nb095_alpha_dummy_069 D R S_cls E), (nb095_alpha_dummy_072 f)),
        ((nb095_alpha_dummy_067 D R S_cls E), (nb095_alpha_dummy_068 f)),
        ((nb095_alpha_dummy_063 D R S_cls E), (nb095_alpha_dummy_065 f)),
        ((nb095_alpha_dummy_064 D R S_cls E), (nb095_alpha_dummy_066 f)),
        ((nb095_alpha_dummy_089 D R S_cls E), (nb095_alpha_dummy_090 f)),
        ((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_071 D R S_cls E), (nb095_alpha_dummy_074 f)),
        ((nb095_alpha_dummy_070 D R S_cls E), (nb095_alpha_dummy_073 f)),
        ((nb095_alpha_dummy_069 D R S_cls E), (nb095_alpha_dummy_072 f)),
        ((nb095_alpha_dummy_067 D R S_cls E), (nb095_alpha_dummy_068 f)),
        ((nb095_alpha_dummy_063 D R S_cls E), (nb095_alpha_dummy_065 f)),
        ((nb095_alpha_dummy_064 D R S_cls E), (nb095_alpha_dummy_066 f)),
        ((nb095_alpha_dummy_089 D R S_cls E), (nb095_alpha_dummy_090 f)),
        ((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_070 D
        R S_cls E) ≠ (nb095_alpha_dummy_081 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_082 f) from (by
          unfold
            nb095_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_081
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_082 f) from (by
          unfold
            nb095_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_071 D
        R S_cls E) ≠ (nb095_alpha_dummy_083 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_084 f) from (by
          unfold
            nb095_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_071 D
        R S_cls E) ≠ (nb095_alpha_dummy_083 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_084 f) from (by
          unfold
            nb095_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_063 D R S_cls E) ≠
                                      (nb095_alpha_dummy_067 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from
                                    (by
                                      unfold nb095_alpha_dummy_068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_067 D R S_cls E),
                                    (nb095_alpha_dummy_068 f)),
                                  ((nb095_alpha_dummy_063 D R S_cls E),
                                    (nb095_alpha_dummy_065 f)),
                                  ((nb095_alpha_dummy_064 D R S_cls E),
                                    (nb095_alpha_dummy_066 f)),
                                  ((nb095_alpha_dummy_089 D R S_cls E),
                                    (nb095_alpha_dummy_090 f)),
                                  ((nb095_alpha_dummy_087 D R S_cls E),
                                    (nb095_alpha_dummy_088 f)),
                                  ((nb095_alpha_dummy_056 D R S_cls E),
                                    (nb095_alpha_dummy_058 f)),
                                  ((nb095_alpha_dummy_055 D R S_cls E),
                                    (nb095_alpha_dummy_057 f)),
                                  ((nb095_alpha_dummy_085 D R S_cls E),
                                    (nb095_alpha_dummy_086 f)),
                                  ((nb095_alpha_dummy_059 D R S_cls E),
                                    (nb095_alpha_dummy_060 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_063 D R S_cls E) ≠
                                    (nb095_alpha_dummy_067 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_067;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from (by
                                    unfold nb095_alpha_dummy_068;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0051 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_063 D R S_cls E) ≠
                                      (nb095_alpha_dummy_067 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from
                                    (by
                                      unfold nb095_alpha_dummy_068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_067 D R S_cls E),
                                    (nb095_alpha_dummy_068 f)),
                                  ((nb095_alpha_dummy_063 D R S_cls E),
                                    (nb095_alpha_dummy_065 f)),
                                  ((nb095_alpha_dummy_064 D R S_cls E),
                                    (nb095_alpha_dummy_066 f)),
                                  ((nb095_alpha_dummy_089 D R S_cls E),
                                    (nb095_alpha_dummy_090 f)),
                                  ((nb095_alpha_dummy_087 D R S_cls E),
                                    (nb095_alpha_dummy_088 f)),
                                  ((nb095_alpha_dummy_056 D R S_cls E),
                                    (nb095_alpha_dummy_058 f)),
                                  ((nb095_alpha_dummy_055 D R S_cls E),
                                    (nb095_alpha_dummy_057 f)),
                                  ((nb095_alpha_dummy_085 D R S_cls E),
                                    (nb095_alpha_dummy_086 f)),
                                  ((nb095_alpha_dummy_059 D R S_cls E),
                                    (nb095_alpha_dummy_060 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                            (nb095_alpha_dummy_063 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_065 f) from (by
                            unfold nb095_alpha_dummy_065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0049 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                              (nb095_alpha_dummy_064 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_064;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_066 f) from (by
                              unfold nb095_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0049 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                                (nb095_alpha_dummy_089 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0078 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_090 f) from (by
                                unfold nb095_alpha_dummy_090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0079 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_056 D R S_cls E) ≠
                                  (nb095_alpha_dummy_087 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_087;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0076 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_058 f) ≠ (nb095_alpha_dummy_088 f) from
                                (by
                                  unfold nb095_alpha_dummy_088;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0077 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_056 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_058 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_070 D R S_cls E) from (by
          unfold nb095_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_073 f) from (by
          unfold nb095_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_069 D R S_cls E) from (by
          unfold nb095_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_072 f) from (by
          unfold nb095_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_063 D R S_cls E) ≠ (nb095_alpha_dummy_067 D R S_cls E) from (by
          unfold nb095_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0050 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from (by
          unfold nb095_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0051 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_071 D R S_cls E), (nb095_alpha_dummy_074 f)),
        ((nb095_alpha_dummy_070 D R S_cls E), (nb095_alpha_dummy_073 f)),
        ((nb095_alpha_dummy_069 D R S_cls E), (nb095_alpha_dummy_072 f)),
        ((nb095_alpha_dummy_067 D R S_cls E), (nb095_alpha_dummy_068 f)),
        ((nb095_alpha_dummy_063 D R S_cls E), (nb095_alpha_dummy_065 f)),
        ((nb095_alpha_dummy_064 D R S_cls E), (nb095_alpha_dummy_066 f)),
        ((nb095_alpha_dummy_089 D R S_cls E), (nb095_alpha_dummy_090 f)),
        ((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠ (nb095_alpha_dummy_077
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_078 f) from (by
          unfold
            nb095_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_075 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_076 f) from (by
          unfold
            nb095_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_071 D R S_cls E), (nb095_alpha_dummy_074 f)),
        ((nb095_alpha_dummy_070 D R S_cls E), (nb095_alpha_dummy_073 f)),
        ((nb095_alpha_dummy_069 D R S_cls E), (nb095_alpha_dummy_072 f)),
        ((nb095_alpha_dummy_067 D R S_cls E), (nb095_alpha_dummy_068 f)),
        ((nb095_alpha_dummy_063 D R S_cls E), (nb095_alpha_dummy_065 f)),
        ((nb095_alpha_dummy_064 D R S_cls E), (nb095_alpha_dummy_066 f)),
        ((nb095_alpha_dummy_089 D R S_cls E), (nb095_alpha_dummy_090 f)),
        ((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_063 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_070 D
        R S_cls E) ≠ (nb095_alpha_dummy_081 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_082 f) from (by
          unfold
            nb095_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠ (nb095_alpha_dummy_081
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_082 f) from (by
          unfold
            nb095_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_070 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_073 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_063
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_065 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_071 D
        R S_cls E) ≠ (nb095_alpha_dummy_083 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_084 f) from (by
          unfold
            nb095_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_071 D
        R S_cls E) ≠ (nb095_alpha_dummy_083 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_084 f) from (by
          unfold
            nb095_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_071 D R S_cls E) ≠
        (nb095_alpha_dummy_079 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_074 f) ≠ (nb095_alpha_dummy_080 f) from (by
          unfold
            nb095_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_063 D R S_cls E) ≠
                                      (nb095_alpha_dummy_067 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from
                                    (by
                                      unfold nb095_alpha_dummy_068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_067 D R S_cls E),
                                    (nb095_alpha_dummy_068 f)),
                                  ((nb095_alpha_dummy_063 D R S_cls E),
                                    (nb095_alpha_dummy_065 f)),
                                  ((nb095_alpha_dummy_064 D R S_cls E),
                                    (nb095_alpha_dummy_066 f)),
                                  ((nb095_alpha_dummy_089 D R S_cls E),
                                    (nb095_alpha_dummy_090 f)),
                                  ((nb095_alpha_dummy_087 D R S_cls E),
                                    (nb095_alpha_dummy_088 f)),
                                  ((nb095_alpha_dummy_056 D R S_cls E),
                                    (nb095_alpha_dummy_058 f)),
                                  ((nb095_alpha_dummy_055 D R S_cls E),
                                    (nb095_alpha_dummy_057 f)),
                                  ((nb095_alpha_dummy_085 D R S_cls E),
                                    (nb095_alpha_dummy_086 f)),
                                  ((nb095_alpha_dummy_059 D R S_cls E),
                                    (nb095_alpha_dummy_060 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_063 D R S_cls E) ≠
                                    (nb095_alpha_dummy_067 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_067;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from (by
                                    unfold nb095_alpha_dummy_068;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0051 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_063 D R S_cls E) ≠
                                      (nb095_alpha_dummy_067 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_065 f) ≠ (nb095_alpha_dummy_068 f) from
                                    (by
                                      unfold nb095_alpha_dummy_068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_067 D R S_cls E),
                                    (nb095_alpha_dummy_068 f)),
                                  ((nb095_alpha_dummy_063 D R S_cls E),
                                    (nb095_alpha_dummy_065 f)),
                                  ((nb095_alpha_dummy_064 D R S_cls E),
                                    (nb095_alpha_dummy_066 f)),
                                  ((nb095_alpha_dummy_089 D R S_cls E),
                                    (nb095_alpha_dummy_090 f)),
                                  ((nb095_alpha_dummy_087 D R S_cls E),
                                    (nb095_alpha_dummy_088 f)),
                                  ((nb095_alpha_dummy_056 D R S_cls E),
                                    (nb095_alpha_dummy_058 f)),
                                  ((nb095_alpha_dummy_055 D R S_cls E),
                                    (nb095_alpha_dummy_057 f)),
                                  ((nb095_alpha_dummy_085 D R S_cls E),
                                    (nb095_alpha_dummy_086 f)),
                                  ((nb095_alpha_dummy_059 D R S_cls E),
                                    (nb095_alpha_dummy_060 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0004 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_103 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_103 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_104 f))
          (Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_104 f))
            (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                      (nb095_alpha_dummy_098 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_100 f) from (by
                      unfold nb095_alpha_dummy_100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                        (nb095_alpha_dummy_097 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_099 f) from (by
                        unfold nb095_alpha_dummy_099;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                          (nb095_alpha_dummy_103 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_104 f) from (by
                          unfold nb095_alpha_dummy_104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                            (nb095_alpha_dummy_101 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_102 f) from (by
                            unfold nb095_alpha_dummy_102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_094 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                              (nb095_alpha_dummy_105 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                              unfold nb095_alpha_dummy_107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                                (nb095_alpha_dummy_106 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from (by
                                unfold nb095_alpha_dummy_108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_112 D R S_cls E) from (by
          unfold nb095_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_115 f) from (by
          unfold nb095_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_111 D R S_cls E) from (by
          unfold nb095_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_114 f) from (by
          unfold nb095_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_112
        D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                      (by
                                        unfold nb095_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_109 D R S_cls E),
                                      (nb095_alpha_dummy_110 f)),
                                    ((nb095_alpha_dummy_105 D R S_cls E),
                                      (nb095_alpha_dummy_107 f)),
                                    ((nb095_alpha_dummy_106 D R S_cls E),
                                      (nb095_alpha_dummy_108 f)),
                                    ((nb095_alpha_dummy_098 D R S_cls E),
                                      (nb095_alpha_dummy_100 f)),
                                    ((nb095_alpha_dummy_097 D R S_cls E),
                                      (nb095_alpha_dummy_099 f)),
                                    ((nb095_alpha_dummy_103 D R S_cls E),
                                      (nb095_alpha_dummy_104 f)),
                                    ((nb095_alpha_dummy_101 D R S_cls E),
                                      (nb095_alpha_dummy_102 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_013 D R S_cls E),
                                      (nb095_alpha_dummy_016 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_009 D R S_cls E),
                                      (nb095_alpha_dummy_010 f)),
                                    ((nb095_alpha_dummy_007 D R S_cls E),
                                      (nb095_alpha_dummy_008 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_105 D R S_cls E) ≠
                                      (nb095_alpha_dummy_109 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                    (by
                                      unfold nb095_alpha_dummy_110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                      (by
                                        unfold nb095_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_109 D R S_cls E),
                                      (nb095_alpha_dummy_110 f)),
                                    ((nb095_alpha_dummy_105 D R S_cls E),
                                      (nb095_alpha_dummy_107 f)),
                                    ((nb095_alpha_dummy_106 D R S_cls E),
                                      (nb095_alpha_dummy_108 f)),
                                    ((nb095_alpha_dummy_098 D R S_cls E),
                                      (nb095_alpha_dummy_100 f)),
                                    ((nb095_alpha_dummy_097 D R S_cls E),
                                      (nb095_alpha_dummy_099 f)),
                                    ((nb095_alpha_dummy_103 D R S_cls E),
                                      (nb095_alpha_dummy_104 f)),
                                    ((nb095_alpha_dummy_101 D R S_cls E),
                                      (nb095_alpha_dummy_102 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_013 D R S_cls E),
                                      (nb095_alpha_dummy_016 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_009 D R S_cls E),
                                      (nb095_alpha_dummy_010 f)),
                                    ((nb095_alpha_dummy_007 D R S_cls E),
                                      (nb095_alpha_dummy_008 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                        (nb095_alpha_dummy_098 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_100 f) from (by
                        unfold nb095_alpha_dummy_100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                          (nb095_alpha_dummy_097 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_099 f) from (by
                          unfold nb095_alpha_dummy_099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                            (nb095_alpha_dummy_103 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_104 f) from (by
                            unfold nb095_alpha_dummy_104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                              (nb095_alpha_dummy_101 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_102 f) from (by
                              unfold nb095_alpha_dummy_102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide))
                            (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_094 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_098 D R S_cls E) ≠
                                (nb095_alpha_dummy_105 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                                unfold nb095_alpha_dummy_107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                                  (nb095_alpha_dummy_106 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0090 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from
                                (by
                                  unfold nb095_alpha_dummy_108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_100 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_112 D R S_cls E) from (by
          unfold nb095_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_115 f) from (by
          unfold nb095_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_111 D R S_cls E) from (by
          unfold nb095_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_114 f) from (by
          unfold nb095_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_112
        D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_110 f) from (by
                                          unfold nb095_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_109 D R S_cls E),
                                        (nb095_alpha_dummy_110 f)),
                                      ((nb095_alpha_dummy_105 D R S_cls E),
                                        (nb095_alpha_dummy_107 f)),
                                      ((nb095_alpha_dummy_106 D R S_cls E),
                                        (nb095_alpha_dummy_108 f)),
                                      ((nb095_alpha_dummy_098 D R S_cls E),
                                        (nb095_alpha_dummy_100 f)),
                                      ((nb095_alpha_dummy_097 D R S_cls E),
                                        (nb095_alpha_dummy_099 f)),
                                      ((nb095_alpha_dummy_103 D R S_cls E),
                                        (nb095_alpha_dummy_104 f)),
                                      ((nb095_alpha_dummy_101 D R S_cls E),
                                        (nb095_alpha_dummy_102 f)),
                                      ((nb095_alpha_dummy_092 D R S_cls E),
                                        (nb095_alpha_dummy_094 f)),
                                      ((nb095_alpha_dummy_091 D R S_cls E),
                                        (nb095_alpha_dummy_093 f)),
                                      ((nb095_alpha_dummy_095 D R S_cls E),
                                        (nb095_alpha_dummy_096 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_009 D R S_cls E),
                                        (nb095_alpha_dummy_010 f)),
                                      ((nb095_alpha_dummy_007 D R S_cls E),
                                        (nb095_alpha_dummy_008 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                      (by
                                        unfold nb095_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_110 f) from (by
                                          unfold nb095_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_109 D R S_cls E),
                                        (nb095_alpha_dummy_110 f)),
                                      ((nb095_alpha_dummy_105 D R S_cls E),
                                        (nb095_alpha_dummy_107 f)),
                                      ((nb095_alpha_dummy_106 D R S_cls E),
                                        (nb095_alpha_dummy_108 f)),
                                      ((nb095_alpha_dummy_098 D R S_cls E),
                                        (nb095_alpha_dummy_100 f)),
                                      ((nb095_alpha_dummy_097 D R S_cls E),
                                        (nb095_alpha_dummy_099 f)),
                                      ((nb095_alpha_dummy_103 D R S_cls E),
                                        (nb095_alpha_dummy_104 f)),
                                      ((nb095_alpha_dummy_101 D R S_cls E),
                                        (nb095_alpha_dummy_102 f)),
                                      ((nb095_alpha_dummy_092 D R S_cls E),
                                        (nb095_alpha_dummy_094 f)),
                                      ((nb095_alpha_dummy_091 D R S_cls E),
                                        (nb095_alpha_dummy_093 f)),
                                      ((nb095_alpha_dummy_095 D R S_cls E),
                                        (nb095_alpha_dummy_096 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_009 D R S_cls E),
                                        (nb095_alpha_dummy_010 f)),
                                      ((nb095_alpha_dummy_007 D R S_cls E),
                                        (nb095_alpha_dummy_008 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0005 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
        ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_131 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_131 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_132 f))
          (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_132 f))
            (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                      (nb095_alpha_dummy_105 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_105;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                      unfold nb095_alpha_dummy_107;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                        (nb095_alpha_dummy_106 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from (by
                        unfold nb095_alpha_dummy_108;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0091 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                          (nb095_alpha_dummy_131 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0120 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_132 f) from (by
                          unfold nb095_alpha_dummy_132;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                            (nb095_alpha_dummy_129 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0118 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_130 f) from (by
                            unfold nb095_alpha_dummy_130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0119 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_112 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0094 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_115 f) from
                                      (by
                                        unfold nb095_alpha_dummy_115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0095 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_111 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0094 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_114 f) from (by
                                          unfold nb095_alpha_dummy_114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0095 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_113 D R S_cls E),
        (nb095_alpha_dummy_116 f)), ((nb095_alpha_dummy_112 D R S_cls E),
        (nb095_alpha_dummy_115 f)), ((nb095_alpha_dummy_111 D R S_cls E),
        (nb095_alpha_dummy_114 f)), ((nb095_alpha_dummy_109 D R S_cls E),
        (nb095_alpha_dummy_110 f)), ((nb095_alpha_dummy_105 D R S_cls E),
        (nb095_alpha_dummy_107 f)), ((nb095_alpha_dummy_106 D R S_cls E),
        (nb095_alpha_dummy_108 f)), ((nb095_alpha_dummy_131 D R S_cls E),
        (nb095_alpha_dummy_132 f)), ((nb095_alpha_dummy_129 D R S_cls E),
        (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_113 D R S_cls E),
        (nb095_alpha_dummy_116 f)), ((nb095_alpha_dummy_112 D R S_cls E),
        (nb095_alpha_dummy_115 f)), ((nb095_alpha_dummy_111 D R S_cls E),
        (nb095_alpha_dummy_114 f)), ((nb095_alpha_dummy_109 D R S_cls E),
        (nb095_alpha_dummy_110 f)), ((nb095_alpha_dummy_105 D R S_cls E),
        (nb095_alpha_dummy_107 f)), ((nb095_alpha_dummy_106 D R S_cls E),
        (nb095_alpha_dummy_108 f)), ((nb095_alpha_dummy_131 D R S_cls E),
        (nb095_alpha_dummy_132 f)), ((nb095_alpha_dummy_129 D R S_cls E),
        (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_123 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_105 D R S_cls E) ≠
                                (nb095_alpha_dummy_109 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                                unfold nb095_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                            ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                            ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                            ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                            ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                            ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                            ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                            ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                            ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                            ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                            ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                            ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
                            ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                            ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                            ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                            ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                            ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
                            ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
                              (nb095_alpha_dummy_109 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_109;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0092 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                              unfold nb095_alpha_dummy_110;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_105 D R S_cls E) ≠
                                (nb095_alpha_dummy_109 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                                unfold nb095_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                            ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                            ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                            ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                            ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                            ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                            ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                            ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                            ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                            ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                            ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                            ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
                            ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                            ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                            ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                            ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                            ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
                            ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                        (nb095_alpha_dummy_105 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                        unfold nb095_alpha_dummy_107;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0091 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                          (nb095_alpha_dummy_106 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                  1))))
                      (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from (by
                          unfold nb095_alpha_dummy_108;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                            (nb095_alpha_dummy_131 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0120 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_132 f) from (by
                            unfold nb095_alpha_dummy_132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                              (nb095_alpha_dummy_129 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0118 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_130 f) from (by
                              unfold nb095_alpha_dummy_130;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0119 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_112 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0094 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_115 f) from (by
                                          unfold nb095_alpha_dummy_115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0095 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_111 D R S_cls E) from (by
          unfold nb095_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_114 f) from (by
          unfold nb095_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_113 D R S_cls E),
        (nb095_alpha_dummy_116 f)), ((nb095_alpha_dummy_112 D R S_cls E),
        (nb095_alpha_dummy_115 f)), ((nb095_alpha_dummy_111 D R S_cls E),
        (nb095_alpha_dummy_114 f)), ((nb095_alpha_dummy_109 D R S_cls E),
        (nb095_alpha_dummy_110 f)), ((nb095_alpha_dummy_105 D R S_cls E),
        (nb095_alpha_dummy_107 f)), ((nb095_alpha_dummy_106 D R S_cls E),
        (nb095_alpha_dummy_108 f)), ((nb095_alpha_dummy_131 D R S_cls E),
        (nb095_alpha_dummy_132 f)), ((nb095_alpha_dummy_129 D R S_cls E),
        (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
        ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_105 D R S_cls E) ≠
                                  (nb095_alpha_dummy_109 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0092 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                (by
                                  unfold nb095_alpha_dummy_110;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                              ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                              ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                              ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                              ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                              ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                              ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                              ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                              ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                              ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                              ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                              ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
                              ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                              ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                              ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                              ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                              ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
                              ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_105 D R S_cls E) ≠
                                (nb095_alpha_dummy_109 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                                unfold nb095_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_105 D R S_cls E) ≠
                                  (nb095_alpha_dummy_109 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0092 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                (by
                                  unfold nb095_alpha_dummy_110;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                              ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                              ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                              ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                              ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                              ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                              ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                              ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                              ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                              ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                              ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                              ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
                              ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                              ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                              ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                              ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                              ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
                              ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
