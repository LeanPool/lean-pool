/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C078C001Part154Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part154`. -/


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
noncomputable def nb078_split_alpha_0134 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
        ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1063))
          (Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1063)) (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1064 h))
          (Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1064 h))
            (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1058) from
                    (by
                      unfold nb078_alpha_dummy_1058;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
                  (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1060 h) from (by
                      unfold nb078_alpha_dummy_1060;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1057) from (by
                        unfold nb078_alpha_dummy_1057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))))
                    (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1059 h) from (by
                        unfold nb078_alpha_dummy_1059;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1102 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1063) from (by
                          unfold nb078_alpha_dummy_1063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1104) 0))))
                      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1064 h) from (by
                          unfold nb078_alpha_dummy_1064;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1105 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1061) from (by
                            unfold nb078_alpha_dummy_1061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1101) 0))))
                        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1062 h) from (by
                            unfold nb078_alpha_dummy_1062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1103 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1065) from (by
                              unfold nb078_alpha_dummy_1065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                          (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1067 h) from (by
                              unfold nb078_alpha_dummy_1067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1066) from (by
                                unfold nb078_alpha_dummy_1066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 1))))
                            (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1068 h) from
                              (by
                                unfold nb078_alpha_dummy_1068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1072) from (by
          unfold nb078_alpha_dummy_1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1075 h) from (by
          unfold nb078_alpha_dummy_1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1071) from (by
          unfold nb078_alpha_dummy_1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1074 h) from (by
          unfold nb078_alpha_dummy_1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from (by
          unfold nb078_alpha_dummy_1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1070 h) from (by
          unfold nb078_alpha_dummy_1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057),
        (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
        ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057),
        (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
        ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                    ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                    ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                    ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                    ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                    ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
                                    ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from (by
                                      unfold nb078_alpha_dummy_1069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1108)
                                              0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                      (nb078_alpha_dummy_1070 h) from (by
                                      unfold nb078_alpha_dummy_1070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1109 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                    ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                    ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                    ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                    ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                    ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
                                    ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1058) from (by
                        unfold nb078_alpha_dummy_1058;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
                    (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1060 h) from (by
                        unfold nb078_alpha_dummy_1060;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1102 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1057) from (by
                          unfold nb078_alpha_dummy_1057;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1100) 0))))
                      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1059 h) from (by
                          unfold nb078_alpha_dummy_1059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1102 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1063) from (by
                            unfold nb078_alpha_dummy_1063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1104) 0))))
                        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1064 h) from (by
                            unfold nb078_alpha_dummy_1064;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1105 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1061) from (by
                              unfold nb078_alpha_dummy_1061;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1101) 0))))
                          (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1062 h) from (by
                              unfold nb078_alpha_dummy_1062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1103 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1065) from (by
                                unfold nb078_alpha_dummy_1065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                            (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1067 h) from
                              (by
                                unfold nb078_alpha_dummy_1067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1066) from (by
                                  unfold nb078_alpha_dummy_1066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1106) 1)))) (show
                                (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1068 h) from (by
                                  unfold nb078_alpha_dummy_1068;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1072) from (by
          unfold nb078_alpha_dummy_1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1075 h) from (by
          unfold nb078_alpha_dummy_1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1071) from (by
          unfold nb078_alpha_dummy_1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1074 h) from (by
          unfold nb078_alpha_dummy_1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1065) ≠
        (nb078_alpha_dummy_1069) from (by
          unfold nb078_alpha_dummy_1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108)
                  0)))) (show (nb078_alpha_dummy_1067 h) ≠ (nb078_alpha_dummy_1070 h) from (by
          unfold nb078_alpha_dummy_1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057),
        (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
        ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057),
        (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
        ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                        (by
                                          unfold nb078_alpha_dummy_1069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1108)
                                                  0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1070 h) from (by
                                          unfold nb078_alpha_dummy_1070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1109 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                      ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                      ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                      ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                      ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                      ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
                                      ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                        (by
                                          unfold nb078_alpha_dummy_1069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1108)
                                                  0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1070 h) from (by
                                          unfold nb078_alpha_dummy_1070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1109 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                      ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                      ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                      ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                      ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                      ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)),
                                      ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part155`. -/


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
noncomputable def nb078_split_alpha_0135 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)),
        ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
        ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
        ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)),
        ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1089))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1089)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1090 h))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1090 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1065) from (by
                              unfold nb078_alpha_dummy_1065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                          (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1067 h) from (by
                              unfold nb078_alpha_dummy_1067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1066) from (by
                                unfold nb078_alpha_dummy_1066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 1))))
                            (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1068 h) from
                              (by
                                unfold nb078_alpha_dummy_1068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1091) from (by
                                  unfold nb078_alpha_dummy_1091;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1136) 0)))) (show
                                (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1092 h) from (by
                                  unfold nb078_alpha_dummy_1092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1137 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1089) from
                                  (by
                                    unfold nb078_alpha_dummy_1089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1134) 0)))) (show
                                  (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1090 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1090;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1135 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1072) from (by
          unfold nb078_alpha_dummy_1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1075 h) from (by
          unfold nb078_alpha_dummy_1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1071) from (by
          unfold nb078_alpha_dummy_1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1074 h) from (by
          unfold nb078_alpha_dummy_1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from (by
          unfold nb078_alpha_dummy_1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1070 h) from (by
          unfold nb078_alpha_dummy_1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089),
        (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
        ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087),
        (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089),
        (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
        ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087),
        (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                    ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                    ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                    ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)),
                                    ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)),
                                    ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                    ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                    ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)),
                                    ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from (by
                                      unfold nb078_alpha_dummy_1069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1108)
                                              0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                      (nb078_alpha_dummy_1070 h) from (by
                                      unfold nb078_alpha_dummy_1070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1109 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                    ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                    ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                    ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)),
                                    ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)),
                                    ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                    ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                    ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)),
                                    ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1065) from (by
                              unfold nb078_alpha_dummy_1065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                          (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1067 h) from (by
                              unfold nb078_alpha_dummy_1067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1066) from (by
                                unfold nb078_alpha_dummy_1066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 1))))
                            (show (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1068 h) from
                              (by
                                unfold nb078_alpha_dummy_1068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1091) from (by
                                  unfold nb078_alpha_dummy_1091;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1136) 0)))) (show
                                (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1092 h) from (by
                                  unfold nb078_alpha_dummy_1092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1137 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1058) ≠ (nb078_alpha_dummy_1089) from
                                  (by
                                    unfold nb078_alpha_dummy_1089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1134) 0)))) (show
                                  (nb078_alpha_dummy_1060 h) ≠ (nb078_alpha_dummy_1090 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1090;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1135 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1072) from (by
          unfold nb078_alpha_dummy_1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1075 h) from (by
          unfold nb078_alpha_dummy_1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1071) from (by
          unfold nb078_alpha_dummy_1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1074 h) from (by
          unfold nb078_alpha_dummy_1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from (by
          unfold nb078_alpha_dummy_1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108) 0)))) (show (nb078_alpha_dummy_1067 h) ≠
        (nb078_alpha_dummy_1070 h) from (by
          unfold nb078_alpha_dummy_1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089),
        (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
        ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087),
        (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1079) from (by
          unfold
            nb078_alpha_dummy_1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1080 h) from (by
          unfold
            nb078_alpha_dummy_1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1077) from (by
          unfold
            nb078_alpha_dummy_1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1078 h) from (by
          unfold
            nb078_alpha_dummy_1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072),
        (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)),
        ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065),
        (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
        ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089),
        (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
        ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087),
        (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1083) from (by
          unfold
            nb078_alpha_dummy_1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1084 h) from (by
          unfold
            nb078_alpha_dummy_1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1072) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1073) ≠ (nb078_alpha_dummy_1085) from (by
          unfold
            nb078_alpha_dummy_1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1086 h) from (by
          unfold
            nb078_alpha_dummy_1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1073) ≠
        (nb078_alpha_dummy_1081) from (by
          unfold
            nb078_alpha_dummy_1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078_alpha_dummy_1076 h) ≠ (nb078_alpha_dummy_1082 h) from (by
          unfold
            nb078_alpha_dummy_1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                    ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                    ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                    ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)),
                                    ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)),
                                    ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                    ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                    ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)),
                                    ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from (by
                                      unfold nb078_alpha_dummy_1069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1108)
                                              0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                      (nb078_alpha_dummy_1070 h) from (by
                                      unfold nb078_alpha_dummy_1070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1109 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1069) from
                                      (by
                                        unfold nb078_alpha_dummy_1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078_alpha_dummy_1067 h) ≠
                                        (nb078_alpha_dummy_1070 h) from (by
                                        unfold nb078_alpha_dummy_1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)),
                                    ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)),
                                    ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)),
                                    ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)),
                                    ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)),
                                    ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
                                    ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
                                    ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)),
                                    ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)),
            ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)),
            ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)),
            ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)),
            ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)),
            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part156`. -/


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
noncomputable def nb078_split_alpha_0136 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1099))
          (Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1099)) (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1100 h))
          (Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1100 h))
            (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1094) from
                    (by
                      unfold nb078_alpha_dummy_1094;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
                  (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1096 h) from (by
                      unfold nb078_alpha_dummy_1096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1093) from (by
                        unfold nb078_alpha_dummy_1093;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))))
                    (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1095 h) from (by
                        unfold nb078_alpha_dummy_1095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1140 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1099) from (by
                          unfold nb078_alpha_dummy_1099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1142) 0))))
                      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1100 h) from (by
                          unfold nb078_alpha_dummy_1100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1143 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1097) from (by
                            unfold nb078_alpha_dummy_1097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1139) 0))))
                        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1098 h) from (by
                            unfold nb078_alpha_dummy_1098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1141 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1051))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1054 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1101) from (by
                              unfold nb078_alpha_dummy_1101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                          (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1103 h) from (by
                              unfold nb078_alpha_dummy_1103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1145 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1102) from (by
                                unfold nb078_alpha_dummy_1102;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1144) 1))))
                            (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1104 h) from
                              (by
                                unfold nb078_alpha_dummy_1104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1145 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1108) from (by
          unfold nb078_alpha_dummy_1108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 1)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1111 h) from (by
          unfold nb078_alpha_dummy_1111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1107) from (by
          unfold nb078_alpha_dummy_1107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 0)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1110 h) from (by
          unfold nb078_alpha_dummy_1110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
          unfold nb078_alpha_dummy_1105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1146) 0)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1106 h) from (by
          unfold nb078_alpha_dummy_1106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1147 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108),
        (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)),
        ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101),
        (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093),
        (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108),
        (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)),
        ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101),
        (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093),
        (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1119) from (by
          unfold
            nb078_alpha_dummy_1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1120 h) from (by
          unfold
            nb078_alpha_dummy_1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1119) from (by
          unfold
            nb078_alpha_dummy_1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1120 h) from (by
          unfold
            nb078_alpha_dummy_1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠ (nb078_alpha_dummy_1121) from (by
          unfold
            nb078_alpha_dummy_1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1122 h) from (by
          unfold
            nb078_alpha_dummy_1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1109) ≠ (nb078_alpha_dummy_1121) from (by
          unfold
            nb078_alpha_dummy_1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1122 h) from (by
          unfold
            nb078_alpha_dummy_1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from
                                      (by
                                        unfold nb078_alpha_dummy_1105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1146)
                                                0)))) (show (nb078_alpha_dummy_1103 h) ≠
                                        (nb078_alpha_dummy_1106 h) from (by
                                        unfold nb078_alpha_dummy_1106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1147 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                                    ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                                    ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                                    ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                                    ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                                    ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
                                    ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                                      unfold nb078_alpha_dummy_1105;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1146)
                                              0)))) (show (nb078_alpha_dummy_1103 h) ≠
                                      (nb078_alpha_dummy_1106 h) from (by
                                      unfold nb078_alpha_dummy_1106;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1147 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from
                                      (by
                                        unfold nb078_alpha_dummy_1105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1146)
                                                0)))) (show (nb078_alpha_dummy_1103 h) ≠
                                        (nb078_alpha_dummy_1106 h) from (by
                                        unfold nb078_alpha_dummy_1106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1147 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                                    ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                                    ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                                    ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                                    ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                                    ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
                                    ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1094) from (by
                        unfold nb078_alpha_dummy_1094;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
                    (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1096 h) from (by
                        unfold nb078_alpha_dummy_1096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1140 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1093) from (by
                          unfold nb078_alpha_dummy_1093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1138) 0))))
                      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1095 h) from (by
                          unfold nb078_alpha_dummy_1095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1140 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1099) from (by
                            unfold nb078_alpha_dummy_1099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1142) 0))))
                        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1100 h) from (by
                            unfold nb078_alpha_dummy_1100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1143 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1097) from (by
                              unfold nb078_alpha_dummy_1097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1139) 0))))
                          (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1098 h) from (by
                              unfold nb078_alpha_dummy_1098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1141 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv
                                      (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv)
                                (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                  ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1051))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1054 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1101) from (by
                                unfold nb078_alpha_dummy_1101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                            (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1103 h) from
                              (by
                                unfold nb078_alpha_dummy_1103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1145 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1102) from (by
                                  unfold nb078_alpha_dummy_1102;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1144) 1)))) (show
                                (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1104 h) from (by
                                  unfold nb078_alpha_dummy_1104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1145 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_1096 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1108) from (by
          unfold nb078_alpha_dummy_1108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 1)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1111 h) from (by
          unfold nb078_alpha_dummy_1111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1107) from (by
          unfold nb078_alpha_dummy_1107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 0)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1110 h) from (by
          unfold nb078_alpha_dummy_1110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1101) ≠
        (nb078_alpha_dummy_1105) from (by
          unfold nb078_alpha_dummy_1105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1146)
                  0)))) (show (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from (by
          unfold nb078_alpha_dummy_1106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1147 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108),
        (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)),
        ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101),
        (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093),
        (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1115) from (by
          unfold
            nb078_alpha_dummy_1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1116 h) from (by
          unfold
            nb078_alpha_dummy_1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1113) from (by
          unfold
            nb078_alpha_dummy_1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1114 h) from (by
          unfold
            nb078_alpha_dummy_1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108),
        (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)),
        ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101),
        (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093),
        (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1119) from (by
          unfold
            nb078_alpha_dummy_1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1120 h) from (by
          unfold
            nb078_alpha_dummy_1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1119) from (by
          unfold
            nb078_alpha_dummy_1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1120 h) from (by
          unfold
            nb078_alpha_dummy_1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1108) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠ (nb078_alpha_dummy_1121) from (by
          unfold
            nb078_alpha_dummy_1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1122 h) from (by
          unfold
            nb078_alpha_dummy_1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1109) ≠ (nb078_alpha_dummy_1121) from (by
          unfold
            nb078_alpha_dummy_1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1122 h) from (by
          unfold
            nb078_alpha_dummy_1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1109) ≠
        (nb078_alpha_dummy_1117) from (by
          unfold
            nb078_alpha_dummy_1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078_alpha_dummy_1112 h) ≠ (nb078_alpha_dummy_1118 h) from (by
          unfold
            nb078_alpha_dummy_1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from
                                        (by
                                          unfold nb078_alpha_dummy_1105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1146)
                                                  0)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1106 h) from (by
                                          unfold nb078_alpha_dummy_1106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1147 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                                      ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                                      ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                                      ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                                      ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                                      ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
                                      ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from
                                      (by
                                        unfold nb078_alpha_dummy_1105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1146)
                                                0)))) (show (nb078_alpha_dummy_1103 h) ≠
                                        (nb078_alpha_dummy_1106 h) from (by
                                        unfold nb078_alpha_dummy_1106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1147 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from
                                        (by
                                          unfold nb078_alpha_dummy_1105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1146)
                                                  0)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1106 h) from (by
                                          unfold nb078_alpha_dummy_1106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1147 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                                      ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                                      ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                                      ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                                      ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                                      ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)),
                                      ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
