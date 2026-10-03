/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part034`. -/


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

@[expose]
noncomputable def nb077_split_alpha_0020 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_073 F I))
          (Class.cab (nb077_alpha_dummy_067 F I)
            (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_073 F I))
            (Class.cab (nb077_alpha_dummy_067 F I)
              (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_074 x))
          (Class.cab (nb077_alpha_dummy_069 x)
            (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_074 x))
            (Class.cab (nb077_alpha_dummy_069 x)
              (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
                      unfold nb077_alpha_dummy_068;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
                  (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_070 x) from (by
                      unfold nb077_alpha_dummy_070;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
                        unfold nb077_alpha_dummy_067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
                    (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_069 x) from (by
                        unfold nb077_alpha_dummy_069;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0054 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_073 F I) from (by
                          unfold nb077_alpha_dummy_073;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0056 F I) 0))))
                      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_074 x) from (by
                          unfold nb077_alpha_dummy_074;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0057 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_071 F I) from (by
                            unfold nb077_alpha_dummy_071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0053 F I) 0))))
                        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_072 x) from (by
                            unfold nb077_alpha_dummy_072;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0055 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
                              ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                                  (syn_c1st))).fv) (by decide)) (freshVar_injective
                            (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                  (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                                  (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_075 F I) from
                            (by
                              unfold nb077_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                          (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_077 x) from (by
                              unfold nb077_alpha_dummy_077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0059 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_076 F I) from (by
                                unfold nb077_alpha_dummy_076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0058 F I) 1))))
                            (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_078 x) from (by
                                unfold nb077_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0059 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_068 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_070 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_082 F I) from
        (by
          unfold nb077_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I) 1)))) (show (nb077_alpha_dummy_077 x) ≠
        (nb077_alpha_dummy_085 x) from (by
          unfold nb077_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_081 F I) from (by
          unfold nb077_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I)
                  0)))) (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_084 x) from (by
          unfold nb077_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from (by
          unfold nb077_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I)
                  0)))) (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from (by
          unfold nb077_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_083 F I), (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I),
        (nb077_alpha_dummy_085 x)), ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)),
        ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
        (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
        (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_083 F I), (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I),
        (nb077_alpha_dummy_085 x)), ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)),
        ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
        (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
        (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_077
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_093 F I) from
        (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_093 F I) from
        (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083
        F I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083
        F I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0060 F I) 0)))) (show
                                      (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from
                                      (by
                                        unfold nb077_alpha_dummy_080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0061 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_079 F I),
                                      (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
                                      (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I),
                                      (nb077_alpha_dummy_078 x)), ((nb077_alpha_dummy_068 F I),
                                      (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
                                      (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I),
                                      (nb077_alpha_dummy_074 x)), ((nb077_alpha_dummy_071 F I),
                                      (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_079;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0060 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from
                                    (by
                                      unfold nb077_alpha_dummy_080;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0061 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0060 F I) 0)))) (show
                                      (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from
                                      (by
                                        unfold nb077_alpha_dummy_080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0061 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_079 F I),
                                      (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
                                      (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I),
                                      (nb077_alpha_dummy_078 x)), ((nb077_alpha_dummy_068 F I),
                                      (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
                                      (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I),
                                      (nb077_alpha_dummy_074 x)), ((nb077_alpha_dummy_071 F I),
                                      (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
                        unfold nb077_alpha_dummy_068;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
                    (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_070 x) from (by
                        unfold nb077_alpha_dummy_070;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0054 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
                          unfold nb077_alpha_dummy_067;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
                      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_069 x) from (by
                          unfold nb077_alpha_dummy_069;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0054 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_073 F I) from (by
                            unfold nb077_alpha_dummy_073;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0056 F I) 0))))
                        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_074 x) from (by
                            unfold nb077_alpha_dummy_074;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0057 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_071 F I) from
                            (by
                              unfold nb077_alpha_dummy_071;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0053 F I) 0))))
                          (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_072 x) from (by
                              unfold nb077_alpha_dummy_072;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0055 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
                                ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                      (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                        (syn_c1c))) (syn_c1st))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                    (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                                    (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_075 F I) from (by
                                unfold nb077_alpha_dummy_075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                            (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_077 x) from (by
                                unfold nb077_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0059 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_076 F I) from
                                (by
                                  unfold nb077_alpha_dummy_076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0058 F I)
                                          1))))
                              (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_078 x) from
                                (by
                                  unfold nb077_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0059 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_068 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_070 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_082 F I) from (by
          unfold nb077_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I)
                  1)))) (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_085 x) from (by
          unfold nb077_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_081 F I) from (by
          unfold nb077_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I)
                  0)))) (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_084 x) from (by
          unfold nb077_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_079 F I) from (by
          unfold nb077_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I)
                  0)))) (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from (by
          unfold nb077_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_083 F I), (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I),
        (nb077_alpha_dummy_085 x)), ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)),
        ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
        (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
        (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_083 F I), (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I),
        (nb077_alpha_dummy_085 x)), ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)),
        ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
        (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
        (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_077
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_093 F I) from
        (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_093 F I) from
        (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083
        F I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083
        F I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_079 F I) from (by
                                          unfold nb077_alpha_dummy_079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0060 F I) 0)))) (show
                                        (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x)
                                        from (by
                                          unfold nb077_alpha_dummy_080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0061 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                                      ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
                                      ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                                      ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
                                      ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                                      ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
                                      ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0060 F I) 0)))) (show
                                      (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from
                                      (by
                                        unfold nb077_alpha_dummy_080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0061 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_079 F I) from (by
                                          unfold nb077_alpha_dummy_079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0060 F I) 0)))) (show
                                        (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x)
                                        from (by
                                          unfold nb077_alpha_dummy_080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0061 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                                      ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
                                      ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                                      ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
                                      ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                                      ((nb077_alpha_dummy_073 F I), (nb077_alpha_dummy_074 x)),
                                      ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part035`. -/


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

@[expose]
noncomputable def nb077_split_alpha_0021 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_101 F I), (nb077_alpha_dummy_102 x)),
        ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
        ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
        ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_101 F I))
          (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_101 F I))
            (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_102 x))
          (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_102 x))
            (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_075 F I) from (by
                      unfold nb077_alpha_dummy_075;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                  (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_077 x) from (by
                      unfold nb077_alpha_dummy_077;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0059 x) 0))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_076 F I) from (by
                        unfold nb077_alpha_dummy_076;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0058 F I) 1))))
                    (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_078 x) from (by
                        unfold nb077_alpha_dummy_078;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0059 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_101 F I) from (by
                          unfold nb077_alpha_dummy_101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0088 F I) 0))))
                      (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_102 x) from (by
                          unfold nb077_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0089 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_099 F I) from (by
                            unfold nb077_alpha_dummy_099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0086 F I) 0))))
                        (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_100 x) from (by
                            unfold nb077_alpha_dummy_100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0087 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_068 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_070 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_082 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_082;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0062 F I) 1)))) (show
                                      (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_085 x) from
                                      (by
                                        unfold nb077_alpha_dummy_085;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0063 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_081 F I) from (by
                                          unfold nb077_alpha_dummy_081;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0062 F I) 0)))) (show
                                        (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_084 x)
                                        from (by
                                          unfold nb077_alpha_dummy_084;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0063 x) 0))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_079 F I) from (by
          unfold nb077_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I) 0)))) (show (nb077_alpha_dummy_077 x) ≠
        (nb077_alpha_dummy_080 x) from (by
          unfold nb077_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_083 F I),
        (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I), (nb077_alpha_dummy_085 x)),
                                        ((nb077_alpha_dummy_081 F I),
        (nb077_alpha_dummy_084 x)), ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                                        ((nb077_alpha_dummy_075 F I),
        (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                                        ((nb077_alpha_dummy_101 F I),
        (nb077_alpha_dummy_102 x)), ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
                                        ((nb077_alpha_dummy_068 F I),
        (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                                        ((nb077_alpha_dummy_097 F I),
        (nb077_alpha_dummy_098 x)), ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                                        ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                        ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                                        ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_089 F I) from (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_089 F I) from (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb077_alpha_dummy_083 F I),
        (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I), (nb077_alpha_dummy_085 x)),
        ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)), ((nb077_alpha_dummy_079 F I),
        (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
        ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)), ((nb077_alpha_dummy_101 F I),
        (nb077_alpha_dummy_102 x)), ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
        (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_093 F I) from (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_093 F I) from (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from (by
                                unfold nb077_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                            (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from (by
                                unfold nb077_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                            ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
                            ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                            ((nb077_alpha_dummy_101 F I), (nb077_alpha_dummy_102 x)),
                            ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
                            ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
                            ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                            ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
                            ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from
                            (by
                              unfold nb077_alpha_dummy_079;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                          (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from (by
                              unfold nb077_alpha_dummy_080;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from (by
                                unfold nb077_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                            (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from (by
                                unfold nb077_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                            ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
                            ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                            ((nb077_alpha_dummy_101 F I), (nb077_alpha_dummy_102 x)),
                            ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
                            ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
                            ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                            ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
                            ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_075 F I) from (by
                        unfold nb077_alpha_dummy_075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                    (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_077 x) from (by
                        unfold nb077_alpha_dummy_077;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0059 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_076 F I) from (by
                          unfold nb077_alpha_dummy_076;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0058 F I) 1))))
                      (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_078 x) from (by
                          unfold nb077_alpha_dummy_078;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0059 x) 1))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_101 F I) from (by
                            unfold nb077_alpha_dummy_101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0088 F I) 0))))
                        (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_102 x) from (by
                            unfold nb077_alpha_dummy_102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0089 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_068 F I) ≠ (nb077_alpha_dummy_099 F I) from
                            (by
                              unfold nb077_alpha_dummy_099;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0086 F I) 0))))
                          (show (nb077_alpha_dummy_070 x) ≠ (nb077_alpha_dummy_100 x) from (by
                              unfold nb077_alpha_dummy_100;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0087 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_068 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_070 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_082 F I) from (by
                                          unfold nb077_alpha_dummy_082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0062 F I) 1)))) (show
                                        (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_085 x)
                                        from (by
                                          unfold nb077_alpha_dummy_085;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0063 x) 1))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_075 F I) ≠
        (nb077_alpha_dummy_081 F I) from (by
          unfold nb077_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I) 0)))) (show (nb077_alpha_dummy_077 x) ≠
        (nb077_alpha_dummy_084 x) from (by
          unfold nb077_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from (by
          unfold nb077_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I) 0)))) (show (nb077_alpha_dummy_077 x) ≠
        (nb077_alpha_dummy_080 x) from (by
          unfold nb077_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_083 F I),
        (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I), (nb077_alpha_dummy_085 x)),
        ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)), ((nb077_alpha_dummy_079 F I),
        (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
        ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)), ((nb077_alpha_dummy_101 F I),
        (nb077_alpha_dummy_102 x)), ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
        ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I),
        (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
        ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_082 F
        I) ≠ (nb077_alpha_dummy_089 F I) from (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠ (nb077_alpha_dummy_089 F I) from
        (by
          unfold
            nb077_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_090 x) from (by
          unfold
            nb077_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_087 F I) from (by
          unfold
            nb077_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_088 x) from (by
          unfold
            nb077_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_083 F I), (nb077_alpha_dummy_086 x)), ((nb077_alpha_dummy_082 F I),
        (nb077_alpha_dummy_085 x)), ((nb077_alpha_dummy_081 F I), (nb077_alpha_dummy_084 x)),
        ((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)), ((nb077_alpha_dummy_075 F I),
        (nb077_alpha_dummy_077 x)), ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
        ((nb077_alpha_dummy_101 F I), (nb077_alpha_dummy_102 x)), ((nb077_alpha_dummy_099 F I),
        (nb077_alpha_dummy_100 x)), ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
        ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)), ((nb077_alpha_dummy_097 F I),
        (nb077_alpha_dummy_098 x)), ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_082 F
        I) ≠ (nb077_alpha_dummy_093 F I) from (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_093 F I) from
        (by
          unfold
            nb077_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_094 x) from (by
          unfold
            nb077_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_082 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_075
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083 F
        I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_083 F
        I) ≠ (nb077_alpha_dummy_095 F I) from (by
          unfold
            nb077_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_096 x) from (by
          unfold
            nb077_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_083 F I) ≠
        (nb077_alpha_dummy_091 F I) from (by
          unfold
            nb077_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077_alpha_dummy_086 x) ≠ (nb077_alpha_dummy_092 x) from (by
          unfold
            nb077_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from
                                (by
                                  unfold nb077_alpha_dummy_079;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0060 F I)
                                          0))))
                              (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from
                                (by
                                  unfold nb077_alpha_dummy_080;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                              ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
                              ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                              ((nb077_alpha_dummy_101 F I), (nb077_alpha_dummy_102 x)),
                              ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
                              ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
                              ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                              ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
                              ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from (by
                                unfold nb077_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                            (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from (by
                                unfold nb077_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_079 F I) from
                                (by
                                  unfold nb077_alpha_dummy_079;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0060 F I)
                                          0))))
                              (show (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_080 x) from
                                (by
                                  unfold nb077_alpha_dummy_080;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_079 F I), (nb077_alpha_dummy_080 x)),
                              ((nb077_alpha_dummy_075 F I), (nb077_alpha_dummy_077 x)),
                              ((nb077_alpha_dummy_076 F I), (nb077_alpha_dummy_078 x)),
                              ((nb077_alpha_dummy_101 F I), (nb077_alpha_dummy_102 x)),
                              ((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)),
                              ((nb077_alpha_dummy_068 F I), (nb077_alpha_dummy_070 x)),
                              ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
                              ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)),
                              ((nb077_alpha_dummy_071 F I), (nb077_alpha_dummy_072 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part036`. -/


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

@[expose]
noncomputable def nb077_split_alpha_0022 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
        ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_109 F I))
          (Class.cab (nb077_alpha_dummy_103 F I)
            (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_109 F I))
            (Class.cab (nb077_alpha_dummy_103 F I)
              (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_110 x))
          (Class.cab (nb077_alpha_dummy_105 x)
            (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_110 x))
            (Class.cab (nb077_alpha_dummy_105 x)
              (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
                      unfold nb077_alpha_dummy_104;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
                  (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_106 x) from (by
                      unfold nb077_alpha_dummy_106;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_103 F I) from (by
                        unfold nb077_alpha_dummy_103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
                    (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_105 x) from (by
                        unfold nb077_alpha_dummy_105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0092 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_109 F I) from (by
                          unfold nb077_alpha_dummy_109;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0094 F I) 0))))
                      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_110 x) from (by
                          unfold nb077_alpha_dummy_110;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0095 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_107 F I) from (by
                            unfold nb077_alpha_dummy_107;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0091 F I) 0))))
                        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_108 x) from (by
                            unfold nb077_alpha_dummy_108;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0093 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
                              ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))
                                  (syn_c1st))).fv) (by decide)) (freshVar_injective
                            (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                  (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                                  (syn_c1st))).fv) (by decide)) (TAlphaVar.there
                            (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                    (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                      (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                        (syn_c1c))) (syn_c1st))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                    (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                                    (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_064 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_104 F I) ≠ (nb077_alpha_dummy_111 F I) from
                            (by
                              unfold nb077_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0096 F I) 0))))
                          (show (nb077_alpha_dummy_106 x) ≠ (nb077_alpha_dummy_113 x) from (by
                              unfold nb077_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0097 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_104 F I) ≠ (nb077_alpha_dummy_112 F I) from (by
                                unfold nb077_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0096 F I) 1))))
                            (show (nb077_alpha_dummy_106 x) ≠ (nb077_alpha_dummy_114 x) from (by
                                unfold nb077_alpha_dummy_114;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0097 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_104 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_106 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_118 F I) from
        (by
          unfold nb077_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I) 1)))) (show (nb077_alpha_dummy_113 x) ≠
        (nb077_alpha_dummy_121 x) from (by
          unfold nb077_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_117 F I) from (by
          unfold nb077_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I)
                  0)))) (show (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_120 x) from (by
          unfold nb077_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_115 F I) from (by
          unfold nb077_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0098 F I)
                  0)))) (show (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x) from (by
          unfold nb077_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0099 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I),
        (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)),
        ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I),
        (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)),
        ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I),
        (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
        ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I),
        (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)),
        ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I),
        (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)),
        ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I),
        (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
        ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_118
        F I) ≠ (nb077_alpha_dummy_129 F I) from (by
          unfold
            nb077_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_130 x) from (by
          unfold
            nb077_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_129 F I) from
        (by
          unfold
            nb077_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_130 x) from (by
          unfold
            nb077_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_119
        F I) ≠ (nb077_alpha_dummy_131 F I) from (by
          unfold
            nb077_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_132 x) from (by
          unfold
            nb077_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_119
        F I) ≠ (nb077_alpha_dummy_131 F I) from (by
          unfold
            nb077_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_132 x) from (by
          unfold
            nb077_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_115 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0098 F I) 0)))) (show
                                      (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x) from
                                      (by
                                        unfold nb077_alpha_dummy_116;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0099 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_115 F I),
                                      (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I),
                                      (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I),
                                      (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I),
                                      (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I),
                                      (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I),
                                      (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I),
                                      (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_115 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_115;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0098 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x) from
                                    (by
                                      unfold nb077_alpha_dummy_116;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0099 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_115 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0098 F I) 0)))) (show
                                      (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x) from
                                      (by
                                        unfold nb077_alpha_dummy_116;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0099 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_115 F I),
                                      (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I),
                                      (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I),
                                      (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I),
                                      (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I),
                                      (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I),
                                      (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I),
                                      (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
                        unfold nb077_alpha_dummy_104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
                    (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_106 x) from (by
                        unfold nb077_alpha_dummy_106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0092 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_103 F I) from (by
                          unfold nb077_alpha_dummy_103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
                      (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_105 x) from (by
                          unfold nb077_alpha_dummy_105;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0092 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_109 F I) from (by
                            unfold nb077_alpha_dummy_109;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0094 F I) 0))))
                        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_110 x) from (by
                            unfold nb077_alpha_dummy_110;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0095 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_107 F I) from
                            (by
                              unfold nb077_alpha_dummy_107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0091 F I) 0))))
                          (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_108 x) from (by
                              unfold nb077_alpha_dummy_108;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0093 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
                                ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                      (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                        (syn_c1c))) (syn_c1st))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                    (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))
                                    (syn_c1st))).fv) (by decide)) (TAlphaVar.there
                              (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom
                                      (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                        (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) (syn_c1st))).fv) (by decide)) (freshVar_injective
                                (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv)
                                        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_064 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_104 F I) ≠ (nb077_alpha_dummy_111 F I) from (by
                                unfold nb077_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0096 F I) 0))))
                            (show (nb077_alpha_dummy_106 x) ≠ (nb077_alpha_dummy_113 x) from (by
                                unfold nb077_alpha_dummy_113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0097 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_104 F I) ≠ (nb077_alpha_dummy_112 F I) from
                                (by
                                  unfold nb077_alpha_dummy_112;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0096 F I)
                                          1))))
                              (show (nb077_alpha_dummy_106 x) ≠ (nb077_alpha_dummy_114 x) from
                                (by
                                  unfold nb077_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0097 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_104 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_106 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_118 F I) from (by
          unfold nb077_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I)
                  1)))) (show (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_121 x) from (by
          unfold nb077_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_117 F I) from (by
          unfold nb077_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I)
                  0)))) (show (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_120 x) from (by
          unfold nb077_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_111 F I) ≠
        (nb077_alpha_dummy_115 F I) from (by
          unfold nb077_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0098 F I)
                  0)))) (show (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x) from (by
          unfold nb077_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0099 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I),
        (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)),
        ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I),
        (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)),
        ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I),
        (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
        ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠ (nb077_alpha_dummy_125 F I) from
        (by
          unfold
            nb077_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_126 x) from (by
          unfold
            nb077_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_123 F I) from (by
          unfold
            nb077_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_124 x) from (by
          unfold
            nb077_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I),
        (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)),
        ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I),
        (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)),
        ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I),
        (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
        ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_118
        F I) ≠ (nb077_alpha_dummy_129 F I) from (by
          unfold
            nb077_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_130 x) from (by
          unfold
            nb077_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_129 F I) from
        (by
          unfold
            nb077_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_130 x) from (by
          unfold
            nb077_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_118 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_119
        F I) ≠ (nb077_alpha_dummy_131 F I) from (by
          unfold
            nb077_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_132 x) from (by
          unfold
            nb077_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_119
        F I) ≠ (nb077_alpha_dummy_131 F I) from (by
          unfold
            nb077_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_132 x) from (by
          unfold
            nb077_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_119 F I) ≠
        (nb077_alpha_dummy_127 F I) from (by
          unfold
            nb077_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077_alpha_dummy_122 x) ≠ (nb077_alpha_dummy_128 x) from (by
          unfold
            nb077_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_111 F I) ≠
        (nb077_alpha_dummy_115 F I) from (by
                                          unfold nb077_alpha_dummy_115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0098 F I) 0)))) (show
                                        (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x)
                                        from (by
                                          unfold nb077_alpha_dummy_116;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0099 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)),
                                      ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)),
                                      ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)),
                                      ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)),
                                      ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
                                      ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
                                      ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_115 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0098 F I) 0)))) (show
                                      (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x) from
                                      (by
                                        unfold nb077_alpha_dummy_116;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0099 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_111 F I) ≠
        (nb077_alpha_dummy_115 F I) from (by
                                          unfold nb077_alpha_dummy_115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0098 F I) 0)))) (show
                                        (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_116 x)
                                        from (by
                                          unfold nb077_alpha_dummy_116;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0099 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)),
                                      ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)),
                                      ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)),
                                      ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)),
                                      ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
                                      ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)),
                                      ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
