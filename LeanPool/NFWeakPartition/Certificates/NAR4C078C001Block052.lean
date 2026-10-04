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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0134`. -/
@[expose]
noncomputable def nb078SplitAlpha0134 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
        ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1063))
          (Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1063)) (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCphi (Class.cv (nb078AlphaDummy1058)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1064 h))
          (Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1064 h))
            (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCphi (Class.cv (nb078AlphaDummy1060 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1058) from
                    (by
                      unfold nb078AlphaDummy1058;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
                  (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1060 h) from (by
                      unfold nb078AlphaDummy1060;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1057) from (by
                        unfold nb078AlphaDummy1057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))))
                    (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1059 h) from (by
                        unfold nb078AlphaDummy1059;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1102 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1063) from (by
                          unfold nb078AlphaDummy1063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1104) 0))))
                      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1064 h) from (by
                          unfold nb078AlphaDummy1064;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1105 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1061) from (by
                            unfold nb078AlphaDummy1061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1101) 0))))
                        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1062 h) from (by
                            unfold nb078AlphaDummy1062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1103 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                              ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1049))).fv ∪
                      ((Class.cv (nb078AlphaDummy1050))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1065) from (by
                              unfold nb078AlphaDummy1065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                          (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1067 h) from (by
                              unfold nb078AlphaDummy1067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1066) from (by
                                unfold nb078AlphaDummy1066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 1))))
                            (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1068 h) from
                              (by
                                unfold nb078AlphaDummy1068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1058))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1072) from (by
          unfold nb078AlphaDummy1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1075 h) from (by
          unfold nb078AlphaDummy1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1071) from (by
          unfold nb078AlphaDummy1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1074 h) from (by
          unfold nb078AlphaDummy1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from (by
          unfold nb078AlphaDummy1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1070 h) from (by
          unfold nb078AlphaDummy1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)), ((nb078AlphaDummy1057),
        (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
        ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)), ((nb078AlphaDummy1057),
        (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
        ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1067
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                    ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                    ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                    ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                    ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                    ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
                                    ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from (by
                                      unfold nb078AlphaDummy1069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1108)
                                              0)))) (show (nb078AlphaDummy1067 h) ≠
                                      (nb078AlphaDummy1070 h) from (by
                                      unfold nb078AlphaDummy1070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1109 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                    ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                    ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                    ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                    ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                    ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
                                    ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1058) from (by
                        unfold nb078AlphaDummy1058;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
                    (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1060 h) from (by
                        unfold nb078AlphaDummy1060;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1102 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1057) from (by
                          unfold nb078AlphaDummy1057;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1100) 0))))
                      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1059 h) from (by
                          unfold nb078AlphaDummy1059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1102 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1063) from (by
                            unfold nb078AlphaDummy1063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1104) 0))))
                        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1064 h) from (by
                            unfold nb078AlphaDummy1064;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1105 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1061) from (by
                              unfold nb078AlphaDummy1061;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1101) 0))))
                          (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1062 h) from (by
                              unfold nb078AlphaDummy1062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1103 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy1049))).fv ∪
                        ((Class.cv (nb078AlphaDummy1050))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1065) from (by
                                unfold nb078AlphaDummy1065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                            (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1067 h) from
                              (by
                                unfold nb078AlphaDummy1067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1066) from (by
                                  unfold nb078AlphaDummy1066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1106) 1)))) (show
                                (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1068 h) from (by
                                  unfold nb078AlphaDummy1068;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy1058))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy1060 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1072) from (by
          unfold nb078AlphaDummy1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1075 h) from (by
          unfold nb078AlphaDummy1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1071) from (by
          unfold nb078AlphaDummy1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1074 h) from (by
          unfold nb078AlphaDummy1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1065) ≠
        (nb078AlphaDummy1069) from (by
          unfold nb078AlphaDummy1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108)
                  0)))) (show (nb078AlphaDummy1067 h) ≠ (nb078AlphaDummy1070 h) from (by
          unfold nb078AlphaDummy1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)), ((nb078AlphaDummy1057),
        (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
        ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)), ((nb078AlphaDummy1057),
        (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
        ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1067
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                        (by
                                          unfold nb078AlphaDummy1069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1108)
                                                  0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1070 h) from (by
                                          unfold nb078AlphaDummy1070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1109 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                      ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                      ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                      ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                      ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                      ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
                                      ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                        (by
                                          unfold nb078AlphaDummy1069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1108)
                                                  0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1070 h) from (by
                                          unfold nb078AlphaDummy1070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1109 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                      ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                      ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                      ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                      ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                      ((nb078AlphaDummy1063), (nb078AlphaDummy1064 h)),
                                      ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0135`. -/
@[expose]
noncomputable def nb078SplitAlpha0135 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1089), (nb078AlphaDummy1090 h)),
        ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
        ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
        ((nb078AlphaDummy1087), (nb078AlphaDummy1088 h)),
        ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1089))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy1058))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1089)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1090 h))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy1060 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1090 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1065) from (by
                              unfold nb078AlphaDummy1065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                          (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1067 h) from (by
                              unfold nb078AlphaDummy1067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1066) from (by
                                unfold nb078AlphaDummy1066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 1))))
                            (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1068 h) from
                              (by
                                unfold nb078AlphaDummy1068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1091) from (by
                                  unfold nb078AlphaDummy1091;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1136) 0)))) (show
                                (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1092 h) from (by
                                  unfold nb078AlphaDummy1092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1137 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1089) from
                                  (by
                                    unfold nb078AlphaDummy1089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1134) 0)))) (show
                                  (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1090 h) from
                                  (by
                                    unfold nb078AlphaDummy1090;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1135 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1058))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1072) from (by
          unfold nb078AlphaDummy1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1075 h) from (by
          unfold nb078AlphaDummy1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1071) from (by
          unfold nb078AlphaDummy1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1074 h) from (by
          unfold nb078AlphaDummy1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from (by
          unfold nb078AlphaDummy1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1070 h) from (by
          unfold nb078AlphaDummy1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)), ((nb078AlphaDummy1089),
        (nb078AlphaDummy1090 h)), ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
        ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1087),
        (nb078AlphaDummy1088 h)), ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)), ((nb078AlphaDummy1089),
        (nb078AlphaDummy1090 h)), ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
        ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1087),
        (nb078AlphaDummy1088 h)), ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1067
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                    ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                    ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                    ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)),
                                    ((nb078AlphaDummy1089), (nb078AlphaDummy1090 h)),
                                    ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                    ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                    ((nb078AlphaDummy1087), (nb078AlphaDummy1088 h)),
                                    ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from (by
                                      unfold nb078AlphaDummy1069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1108)
                                              0)))) (show (nb078AlphaDummy1067 h) ≠
                                      (nb078AlphaDummy1070 h) from (by
                                      unfold nb078AlphaDummy1070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1109 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                    ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                    ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                    ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)),
                                    ((nb078AlphaDummy1089), (nb078AlphaDummy1090 h)),
                                    ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                    ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                    ((nb078AlphaDummy1087), (nb078AlphaDummy1088 h)),
                                    ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1065) from (by
                              unfold nb078AlphaDummy1065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1106) 0))))
                          (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1067 h) from (by
                              unfold nb078AlphaDummy1067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1107 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1066) from (by
                                unfold nb078AlphaDummy1066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1106) 1))))
                            (show (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1068 h) from
                              (by
                                unfold nb078AlphaDummy1068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1107 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1091) from (by
                                  unfold nb078AlphaDummy1091;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1136) 0)))) (show
                                (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1092 h) from (by
                                  unfold nb078AlphaDummy1092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1137 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1058) ≠ (nb078AlphaDummy1089) from
                                  (by
                                    unfold nb078AlphaDummy1089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1134) 0)))) (show
                                  (nb078AlphaDummy1060 h) ≠ (nb078AlphaDummy1090 h) from
                                  (by
                                    unfold nb078AlphaDummy1090;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1135 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1058))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1072) from (by
          unfold nb078AlphaDummy1072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 1)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1075 h) from (by
          unfold nb078AlphaDummy1075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1071) from (by
          unfold nb078AlphaDummy1071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1110) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1074 h) from (by
          unfold nb078AlphaDummy1074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1111 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from (by
          unfold nb078AlphaDummy1069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1108) 0)))) (show (nb078AlphaDummy1067 h) ≠
        (nb078AlphaDummy1070 h) from (by
          unfold nb078AlphaDummy1070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1109 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)), ((nb078AlphaDummy1089),
        (nb078AlphaDummy1090 h)), ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
        ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1087),
        (nb078AlphaDummy1088 h)), ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1114)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1115
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1112)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1113
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1079) from (by
          unfold
            nb078AlphaDummy1079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1118)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1080 h) from (by
          unfold
            nb078AlphaDummy1080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1119
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1077) from (by
          unfold
            nb078AlphaDummy1077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1116)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1078 h) from (by
          unfold
            nb078AlphaDummy1078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1117
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1073), (nb078AlphaDummy1076 h)), ((nb078AlphaDummy1072),
        (nb078AlphaDummy1075 h)), ((nb078AlphaDummy1071), (nb078AlphaDummy1074 h)),
        ((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)), ((nb078AlphaDummy1065),
        (nb078AlphaDummy1067 h)), ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
        ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)), ((nb078AlphaDummy1089),
        (nb078AlphaDummy1090 h)), ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
        ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)), ((nb078AlphaDummy1087),
        (nb078AlphaDummy1088 h)), ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1065))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1067
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1072) ≠ (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1083) from (by
          unfold
            nb078AlphaDummy1083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1122)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1084 h) from (by
          unfold
            nb078AlphaDummy1084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1123
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1072) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1120)
                  0)))) (show (nb078AlphaDummy1075 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1121
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1073) ≠ (nb078AlphaDummy1085) from (by
          unfold
            nb078AlphaDummy1085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1126)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1086 h) from (by
          unfold
            nb078AlphaDummy1086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1127
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1073) ≠
        (nb078AlphaDummy1081) from (by
          unfold
            nb078AlphaDummy1081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1124)
                  0)))) (show (nb078AlphaDummy1076 h) ≠ (nb078AlphaDummy1082 h) from (by
          unfold
            nb078AlphaDummy1082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1125
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                    ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                    ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                    ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)),
                                    ((nb078AlphaDummy1089), (nb078AlphaDummy1090 h)),
                                    ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                    ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                    ((nb078AlphaDummy1087), (nb078AlphaDummy1088 h)),
                                    ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from (by
                                      unfold nb078AlphaDummy1069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1108)
                                              0)))) (show (nb078AlphaDummy1067 h) ≠
                                      (nb078AlphaDummy1070 h) from (by
                                      unfold nb078AlphaDummy1070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1109 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1065) ≠ (nb078AlphaDummy1069) from
                                      (by
                                        unfold nb078AlphaDummy1069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1108)
                                                0)))) (show (nb078AlphaDummy1067 h) ≠
                                        (nb078AlphaDummy1070 h) from (by
                                        unfold nb078AlphaDummy1070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1109 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1069), (nb078AlphaDummy1070 h)),
                                    ((nb078AlphaDummy1065), (nb078AlphaDummy1067 h)),
                                    ((nb078AlphaDummy1066), (nb078AlphaDummy1068 h)),
                                    ((nb078AlphaDummy1091), (nb078AlphaDummy1092 h)),
                                    ((nb078AlphaDummy1089), (nb078AlphaDummy1090 h)),
                                    ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
                                    ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
                                    ((nb078AlphaDummy1087), (nb078AlphaDummy1088 h)),
                                    ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1089), (nb078AlphaDummy1090 h)),
            ((nb078AlphaDummy1058), (nb078AlphaDummy1060 h)),
            ((nb078AlphaDummy1057), (nb078AlphaDummy1059 h)),
            ((nb078AlphaDummy1087), (nb078AlphaDummy1088 h)),
            ((nb078AlphaDummy1061), (nb078AlphaDummy1062 h)),
            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0136`. -/
@[expose]
noncomputable def nb078SplitAlpha0136 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1099))
          (Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1099)) (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCphi (Class.cv (nb078AlphaDummy1094)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1100 h))
          (Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1100 h))
            (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCphi (Class.cv (nb078AlphaDummy1096 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1094) from
                    (by
                      unfold nb078AlphaDummy1094;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
                  (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1096 h) from (by
                      unfold nb078AlphaDummy1096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1093) from (by
                        unfold nb078AlphaDummy1093;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))))
                    (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1095 h) from (by
                        unfold nb078AlphaDummy1095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1140 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1099) from (by
                          unfold nb078AlphaDummy1099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1142) 0))))
                      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1100 h) from (by
                          unfold nb078AlphaDummy1100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1143 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1097) from (by
                            unfold nb078AlphaDummy1097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1139) 0))))
                        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1098 h) from (by
                            unfold nb078AlphaDummy1098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1141 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                              ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1049))).fv ∪
                      ((Class.cv (nb078AlphaDummy1051))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy1054 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1101) from (by
                              unfold nb078AlphaDummy1101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                          (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1103 h) from (by
                              unfold nb078AlphaDummy1103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1145 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1102) from (by
                                unfold nb078AlphaDummy1102;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1144) 1))))
                            (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1104 h) from
                              (by
                                unfold nb078AlphaDummy1104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1145 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1094))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1096 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1108) from (by
          unfold nb078AlphaDummy1108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 1)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1111 h) from (by
          unfold nb078AlphaDummy1111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1107) from (by
          unfold nb078AlphaDummy1107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 0)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1110 h) from (by
          unfold nb078AlphaDummy1110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
          unfold nb078AlphaDummy1105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1146) 0)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1106 h) from (by
          unfold nb078AlphaDummy1106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1147 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1109), (nb078AlphaDummy1112 h)), ((nb078AlphaDummy1108),
        (nb078AlphaDummy1111 h)), ((nb078AlphaDummy1107), (nb078AlphaDummy1110 h)),
        ((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)), ((nb078AlphaDummy1101),
        (nb078AlphaDummy1103 h)), ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093),
        (nb078AlphaDummy1095 h)), ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1109), (nb078AlphaDummy1112 h)), ((nb078AlphaDummy1108),
        (nb078AlphaDummy1111 h)), ((nb078AlphaDummy1107), (nb078AlphaDummy1110 h)),
        ((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)), ((nb078AlphaDummy1101),
        (nb078AlphaDummy1103 h)), ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093),
        (nb078AlphaDummy1095 h)), ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1101))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1103
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1119) from (by
          unfold
            nb078AlphaDummy1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1120 h) from (by
          unfold
            nb078AlphaDummy1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1119) from (by
          unfold
            nb078AlphaDummy1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1120 h) from (by
          unfold
            nb078AlphaDummy1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1109) ≠ (nb078AlphaDummy1121) from (by
          unfold
            nb078AlphaDummy1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1122 h) from (by
          unfold
            nb078AlphaDummy1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1109) ≠ (nb078AlphaDummy1121) from (by
          unfold
            nb078AlphaDummy1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1122 h) from (by
          unfold
            nb078AlphaDummy1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from
                                      (by
                                        unfold nb078AlphaDummy1105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1146)
                                                0)))) (show (nb078AlphaDummy1103 h) ≠
                                        (nb078AlphaDummy1106 h) from (by
                                        unfold nb078AlphaDummy1106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1147 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                                    ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                                    ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                                    ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                                    ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                                    ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
                                    ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                                      unfold nb078AlphaDummy1105;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1146)
                                              0)))) (show (nb078AlphaDummy1103 h) ≠
                                      (nb078AlphaDummy1106 h) from (by
                                      unfold nb078AlphaDummy1106;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1147 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from
                                      (by
                                        unfold nb078AlphaDummy1105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1146)
                                                0)))) (show (nb078AlphaDummy1103 h) ≠
                                        (nb078AlphaDummy1106 h) from (by
                                        unfold nb078AlphaDummy1106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1147 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                                    ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                                    ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                                    ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                                    ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                                    ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
                                    ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1094) from (by
                        unfold nb078AlphaDummy1094;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
                    (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1096 h) from (by
                        unfold nb078AlphaDummy1096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1140 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1093) from (by
                          unfold nb078AlphaDummy1093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1138) 0))))
                      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1095 h) from (by
                          unfold nb078AlphaDummy1095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1140 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1099) from (by
                            unfold nb078AlphaDummy1099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1142) 0))))
                        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1100 h) from (by
                            unfold nb078AlphaDummy1100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1143 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1097) from (by
                              unfold nb078AlphaDummy1097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1139) 0))))
                          (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1098 h) from (by
                              unfold nb078AlphaDummy1098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1141 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv
                                      (synCcnv (Class.cv (nb078AlphaDummy002))))).fv)
                                (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv ∪
                                  ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy1049))).fv ∪
                        ((Class.cv (nb078AlphaDummy1051))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy1054 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1101) from (by
                                unfold nb078AlphaDummy1101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                            (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1103 h) from
                              (by
                                unfold nb078AlphaDummy1103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1145 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1102) from (by
                                  unfold nb078AlphaDummy1102;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1144) 1)))) (show
                                (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1104 h) from (by
                                  unfold nb078AlphaDummy1104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1145 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy1094))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy1096 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1108) from (by
          unfold nb078AlphaDummy1108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 1)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1111 h) from (by
          unfold nb078AlphaDummy1111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1107) from (by
          unfold nb078AlphaDummy1107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1148) 0)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1110 h) from (by
          unfold nb078AlphaDummy1110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1149 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1101) ≠
        (nb078AlphaDummy1105) from (by
          unfold nb078AlphaDummy1105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1146)
                  0)))) (show (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from (by
          unfold nb078AlphaDummy1106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1147 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1109), (nb078AlphaDummy1112 h)), ((nb078AlphaDummy1108),
        (nb078AlphaDummy1111 h)), ((nb078AlphaDummy1107), (nb078AlphaDummy1110 h)),
        ((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)), ((nb078AlphaDummy1101),
        (nb078AlphaDummy1103 h)), ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093),
        (nb078AlphaDummy1095 h)), ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1152)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1153
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1150)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1151
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1115) from (by
          unfold
            nb078AlphaDummy1115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1156)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1116 h) from (by
          unfold
            nb078AlphaDummy1116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1157
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1113) from (by
          unfold
            nb078AlphaDummy1113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1154)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1114 h) from (by
          unfold
            nb078AlphaDummy1114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1155
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1109), (nb078AlphaDummy1112 h)), ((nb078AlphaDummy1108),
        (nb078AlphaDummy1111 h)), ((nb078AlphaDummy1107), (nb078AlphaDummy1110 h)),
        ((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)), ((nb078AlphaDummy1101),
        (nb078AlphaDummy1103 h)), ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093),
        (nb078AlphaDummy1095 h)), ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1101))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1103
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1119) from (by
          unfold
            nb078AlphaDummy1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1120 h) from (by
          unfold
            nb078AlphaDummy1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1119) from (by
          unfold
            nb078AlphaDummy1119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1160)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1120 h) from (by
          unfold
            nb078AlphaDummy1120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1161
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1108) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1158)
                  0)))) (show (nb078AlphaDummy1111 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1159
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1109) ≠ (nb078AlphaDummy1121) from (by
          unfold
            nb078AlphaDummy1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1122 h) from (by
          unfold
            nb078AlphaDummy1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1109) ≠ (nb078AlphaDummy1121) from (by
          unfold
            nb078AlphaDummy1121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1164)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1122 h) from (by
          unfold
            nb078AlphaDummy1122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1165
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1109) ≠
        (nb078AlphaDummy1117) from (by
          unfold
            nb078AlphaDummy1117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1162)
                  0)))) (show (nb078AlphaDummy1112 h) ≠ (nb078AlphaDummy1118 h) from (by
          unfold
            nb078AlphaDummy1118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1163
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from
                                        (by
                                          unfold nb078AlphaDummy1105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1146)
                                                  0)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1106 h) from (by
                                          unfold nb078AlphaDummy1106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1147 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                                      ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                                      ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                                      ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                                      ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                                      ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
                                      ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from
                                      (by
                                        unfold nb078AlphaDummy1105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1146)
                                                0)))) (show (nb078AlphaDummy1103 h) ≠
                                        (nb078AlphaDummy1106 h) from (by
                                        unfold nb078AlphaDummy1106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1147 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from
                                        (by
                                          unfold nb078AlphaDummy1105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1146)
                                                  0)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1106 h) from (by
                                          unfold nb078AlphaDummy1106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1147 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                                      ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                                      ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                                      ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                                      ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                                      ((nb078AlphaDummy1099), (nb078AlphaDummy1100 h)),
                                      ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
