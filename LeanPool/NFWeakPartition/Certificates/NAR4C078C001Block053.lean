/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block052

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part157`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0137`. -/
@[expose]
noncomputable def nb078SplitAlpha0137 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
        ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
        ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
        ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1127))
          (synCphi (Class.cv (nb078AlphaDummy1094)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1127))
            (synCphi (Class.cv (nb078AlphaDummy1094))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1128 h))
          (synCphi (Class.cv (nb078AlphaDummy1096 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1128 h))
            (synCphi (Class.cv (nb078AlphaDummy1096 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1101) from
                    (by
                      unfold nb078AlphaDummy1101;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                  (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1103 h) from (by
                      unfold nb078AlphaDummy1103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1145 h) 0))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1102) from (by
                        unfold nb078AlphaDummy1102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 1))))
                    (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1104 h) from (by
                        unfold nb078AlphaDummy1104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1145 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1127) from (by
                          unfold nb078AlphaDummy1127;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1174) 0))))
                      (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1128 h) from (by
                          unfold nb078AlphaDummy1128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1175 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1125) from (by
                            unfold nb078AlphaDummy1125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1172) 0))))
                        (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1126 h) from (by
                            unfold nb078AlphaDummy1126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1173 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1094))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb078AlphaDummy1096 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1108) from
                                      (by
                                        unfold nb078AlphaDummy1108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1148)
                                                1)))) (show (nb078AlphaDummy1103 h) ≠
                                        (nb078AlphaDummy1111 h) from (by
                                        unfold nb078AlphaDummy1111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1149 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1107) from
                                        (by
                                          unfold nb078AlphaDummy1107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1148)
                                                  0)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1110 h) from (by
                                          unfold nb078AlphaDummy1110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1149 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1101) ≠
        (nb078AlphaDummy1105) from (by
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
                  (nb078_support_mem_1147 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy1109),
        (nb078AlphaDummy1112 h)), ((nb078AlphaDummy1108), (nb078AlphaDummy1111 h)),
                                        ((nb078AlphaDummy1107), (nb078AlphaDummy1110 h)),
                                        ((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                                        ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                                        ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                                        ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
                                        ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
                                        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                                        ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                                        ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
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
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1115) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                        [((nb078AlphaDummy1109), (nb078AlphaDummy1112 h)),
        ((nb078AlphaDummy1108), (nb078AlphaDummy1111 h)), ((nb078AlphaDummy1107),
        (nb078AlphaDummy1110 h)), ((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
        ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)), ((nb078AlphaDummy1102),
        (nb078AlphaDummy1104 h)), ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
        ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)), ((nb078AlphaDummy1094),
        (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
        ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)), ((nb078AlphaDummy1097),
        (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                                unfold nb078AlphaDummy1105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                            (show (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from
                              (by
                                unfold nb078AlphaDummy1106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                            ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                            ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                            ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
                            ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
                            ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                            ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                            ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
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
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                              unfold nb078AlphaDummy1105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                          (show (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from (by
                              unfold nb078AlphaDummy1106;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                                unfold nb078AlphaDummy1105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                            (show (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from
                              (by
                                unfold nb078AlphaDummy1106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                            ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                            ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                            ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
                            ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
                            ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                            ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                            ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
                            ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1101) from (by
                        unfold nb078AlphaDummy1101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                    (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1103 h) from (by
                        unfold nb078AlphaDummy1103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1145 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1102) from (by
                          unfold nb078AlphaDummy1102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1144) 1))))
                      (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1104 h) from (by
                          unfold nb078AlphaDummy1104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1145 h) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1127) from (by
                            unfold nb078AlphaDummy1127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1174) 0))))
                        (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1128 h) from (by
                            unfold nb078AlphaDummy1128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1175 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1094) ≠ (nb078AlphaDummy1125) from (by
                              unfold nb078AlphaDummy1125;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1172) 0))))
                          (show (nb078AlphaDummy1096 h) ≠ (nb078AlphaDummy1126 h) from (by
                              unfold nb078AlphaDummy1126;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1173 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1094))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1096 h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb078AlphaDummy1101) ≠
        (nb078AlphaDummy1108) from (by
                                          unfold nb078AlphaDummy1108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1148)
                                                  1)))) (show (nb078AlphaDummy1103 h) ≠
        (nb078AlphaDummy1111 h) from (by
                                          unfold nb078AlphaDummy1111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1149 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1101) ≠
        (nb078AlphaDummy1107) from (by
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
                  (nb078_support_mem_1147 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy1109),
        (nb078AlphaDummy1112 h)), ((nb078AlphaDummy1108), (nb078AlphaDummy1111 h)),
        ((nb078AlphaDummy1107), (nb078AlphaDummy1110 h)), ((nb078AlphaDummy1105),
        (nb078AlphaDummy1106 h)), ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
        ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)), ((nb078AlphaDummy1127),
        (nb078AlphaDummy1128 h)), ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
        ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093),
        (nb078AlphaDummy1095 h)), ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
        ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1108) ≠ (nb078AlphaDummy1115) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)), ((nb078AlphaDummy1125),
        (nb078AlphaDummy1126 h)), ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
        ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)), ((nb078AlphaDummy1123),
        (nb078AlphaDummy1124 h)), ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                                  unfold nb078AlphaDummy1105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1146) 0)))) (show
                                (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from (by
                                  unfold nb078AlphaDummy1106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                              ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                              ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                              ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
                              ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
                              ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                              ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                              ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                                unfold nb078AlphaDummy1105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                            (show (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from
                              (by
                                unfold nb078AlphaDummy1106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy1101) ≠ (nb078AlphaDummy1105) from (by
                                  unfold nb078AlphaDummy1105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1146) 0)))) (show
                                (nb078AlphaDummy1103 h) ≠ (nb078AlphaDummy1106 h) from (by
                                  unfold nb078AlphaDummy1106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy1105), (nb078AlphaDummy1106 h)),
                              ((nb078AlphaDummy1101), (nb078AlphaDummy1103 h)),
                              ((nb078AlphaDummy1102), (nb078AlphaDummy1104 h)),
                              ((nb078AlphaDummy1127), (nb078AlphaDummy1128 h)),
                              ((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)),
                              ((nb078AlphaDummy1094), (nb078AlphaDummy1096 h)),
                              ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
                              ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)),
                              ((nb078AlphaDummy1097), (nb078AlphaDummy1098 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                              ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part158`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0138`. -/
@[expose]
noncomputable def nb078SplitAlpha0138 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1141))
          (Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1141)) (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCphi (Class.cv (nb078AlphaDummy1136)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1142 h))
          (Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1142 h))
            (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCphi (Class.cv (nb078AlphaDummy1138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1136) from
                    (by
                      unfold nb078AlphaDummy1136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
                  (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1138 h) from (by
                      unfold nb078AlphaDummy1138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 1))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1135) from (by
                        unfold nb078AlphaDummy1135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 0))))
                    (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1137 h) from (by
                        unfold nb078AlphaDummy1137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1182 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1141) from (by
                          unfold nb078AlphaDummy1141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1184) 0))))
                      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1142 h) from (by
                          unfold nb078AlphaDummy1142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1185 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1139) from (by
                            unfold nb078AlphaDummy1139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1181) 0))))
                        (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1140 h) from (by
                            unfold nb078AlphaDummy1140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1183 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                          (freshVar_injective (((synCcnv (Class.cv h))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1129))).fv ∪
                      ((Class.cv (nb078AlphaDummy1130))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy1132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1143) from (by
                              unfold nb078AlphaDummy1143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                          (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1145 h) from (by
                              unfold nb078AlphaDummy1145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1187 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1144) from (by
                                unfold nb078AlphaDummy1144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1186) 1))))
                            (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1146 h) from
                              (by
                                unfold nb078AlphaDummy1146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1187 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1136))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1150) from (by
          unfold nb078AlphaDummy1150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 1)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1153 h) from (by
          unfold nb078AlphaDummy1153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1149) from (by
          unfold nb078AlphaDummy1149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1152 h) from (by
          unfold nb078AlphaDummy1152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
          unfold nb078AlphaDummy1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188) 0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1148 h) from (by
          unfold nb078AlphaDummy1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1151), (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150),
        (nb078AlphaDummy1153 h)), ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)),
        ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)), ((nb078AlphaDummy1143),
        (nb078AlphaDummy1145 h)), ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135),
        (nb078AlphaDummy1137 h)), ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1151), (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150),
        (nb078AlphaDummy1153 h)), ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)),
        ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)), ((nb078AlphaDummy1143),
        (nb078AlphaDummy1145 h)), ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135),
        (nb078AlphaDummy1137 h)), ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1143))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1145
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from
                                      (by
                                        unfold nb078AlphaDummy1147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1188)
                                                0)))) (show (nb078AlphaDummy1145 h) ≠
                                        (nb078AlphaDummy1148 h) from (by
                                        unfold nb078AlphaDummy1148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1189 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                                    ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                                    ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                                    ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                                    ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                                    ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
                                    ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
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
                                    (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                                      unfold nb078AlphaDummy1147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1188)
                                              0)))) (show (nb078AlphaDummy1145 h) ≠
                                      (nb078AlphaDummy1148 h) from (by
                                      unfold nb078AlphaDummy1148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1189 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from
                                      (by
                                        unfold nb078AlphaDummy1147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1188)
                                                0)))) (show (nb078AlphaDummy1145 h) ≠
                                        (nb078AlphaDummy1148 h) from (by
                                        unfold nb078AlphaDummy1148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1189 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                                    ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                                    ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                                    ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                                    ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                                    ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
                                    ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
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
                    (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1136) from (by
                        unfold nb078AlphaDummy1136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
                    (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1138 h) from (by
                        unfold nb078AlphaDummy1138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1182 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1135) from (by
                          unfold nb078AlphaDummy1135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1180) 0))))
                      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1137 h) from (by
                          unfold nb078AlphaDummy1137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1182 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1141) from (by
                            unfold nb078AlphaDummy1141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1184) 0))))
                        (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1142 h) from (by
                            unfold nb078AlphaDummy1142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1185 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1139) from (by
                              unfold nb078AlphaDummy1139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1181) 0))))
                          (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1140 h) from (by
                              unfold nb078AlphaDummy1140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1183 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                            (freshVar_injective (((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy1129))).fv ∪
                        ((Class.cv (nb078AlphaDummy1130))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy1132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1143) from (by
                                unfold nb078AlphaDummy1143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                            (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1145 h) from
                              (by
                                unfold nb078AlphaDummy1145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1187 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1144) from (by
                                  unfold nb078AlphaDummy1144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1186) 1)))) (show
                                (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1146 h) from (by
                                  unfold nb078AlphaDummy1146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1187 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy1136))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy1138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1150) from (by
          unfold nb078AlphaDummy1150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 1)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1153 h) from (by
          unfold nb078AlphaDummy1153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1149) from (by
          unfold nb078AlphaDummy1149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1152 h) from (by
          unfold nb078AlphaDummy1152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1143) ≠
        (nb078AlphaDummy1147) from (by
          unfold nb078AlphaDummy1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188)
                  0)))) (show (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from (by
          unfold nb078AlphaDummy1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1151), (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150),
        (nb078AlphaDummy1153 h)), ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)),
        ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)), ((nb078AlphaDummy1143),
        (nb078AlphaDummy1145 h)), ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135),
        (nb078AlphaDummy1137 h)), ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1151), (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150),
        (nb078AlphaDummy1153 h)), ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)),
        ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)), ((nb078AlphaDummy1143),
        (nb078AlphaDummy1145 h)), ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135),
        (nb078AlphaDummy1137 h)), ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1143))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1145
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from
                                        (by
                                          unfold nb078AlphaDummy1147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1188)
                                                  0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1148 h) from (by
                                          unfold nb078AlphaDummy1148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1189 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                                      ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                                      ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                                      ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                                      ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                                      ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
                                      ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
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
                                      (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from
                                      (by
                                        unfold nb078AlphaDummy1147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1188)
                                                0)))) (show (nb078AlphaDummy1145 h) ≠
                                        (nb078AlphaDummy1148 h) from (by
                                        unfold nb078AlphaDummy1148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1189 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from
                                        (by
                                          unfold nb078AlphaDummy1147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1188)
                                                  0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1148 h) from (by
                                          unfold nb078AlphaDummy1148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1189 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                                      ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                                      ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                                      ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                                      ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                                      ((nb078AlphaDummy1141), (nb078AlphaDummy1142 h)),
                                      ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
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

/-! Certificates from `NAR4C078C001Part159`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0139`. -/
@[expose]
noncomputable def nb078SplitAlpha0139 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
        ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
        ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
        ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1169))
          (synCphi (Class.cv (nb078AlphaDummy1136)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1169))
            (synCphi (Class.cv (nb078AlphaDummy1136))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1170 h))
          (synCphi (Class.cv (nb078AlphaDummy1138 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1170 h))
            (synCphi (Class.cv (nb078AlphaDummy1138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1143) from
                    (by
                      unfold nb078AlphaDummy1143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                  (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1145 h) from (by
                      unfold nb078AlphaDummy1145;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1187 h) 0))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1144) from (by
                        unfold nb078AlphaDummy1144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 1))))
                    (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1146 h) from (by
                        unfold nb078AlphaDummy1146;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1187 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1169) from (by
                          unfold nb078AlphaDummy1169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1216) 0))))
                      (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1170 h) from (by
                          unfold nb078AlphaDummy1170;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1217 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1167) from (by
                            unfold nb078AlphaDummy1167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1214) 0))))
                        (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1168 h) from (by
                            unfold nb078AlphaDummy1168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1215 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1136))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb078AlphaDummy1138 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1150) from
                                      (by
                                        unfold nb078AlphaDummy1150;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1190)
                                                1)))) (show (nb078AlphaDummy1145 h) ≠
                                        (nb078AlphaDummy1153 h) from (by
                                        unfold nb078AlphaDummy1153;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1191 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1149) from
                                        (by
                                          unfold nb078AlphaDummy1149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1190)
                                                  0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1152 h) from (by
                                          unfold nb078AlphaDummy1152;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1191 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1143) ≠
        (nb078AlphaDummy1147) from (by
          unfold nb078AlphaDummy1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188) 0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1148 h) from (by
          unfold nb078AlphaDummy1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy1151),
        (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150), (nb078AlphaDummy1153 h)),
                                        ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)),
                                        ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                                        ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                                        ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                                        ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
                                        ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
                                        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                                        ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                                        ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
                                        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                                        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                        ((nb078AlphaDummy002), h),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy1151), (nb078AlphaDummy1154 h)),
        ((nb078AlphaDummy1150), (nb078AlphaDummy1153 h)), ((nb078AlphaDummy1149),
        (nb078AlphaDummy1152 h)), ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
        ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)), ((nb078AlphaDummy1144),
        (nb078AlphaDummy1146 h)), ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
        ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)), ((nb078AlphaDummy1136),
        (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
        ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)), ((nb078AlphaDummy1139),
        (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                                unfold nb078AlphaDummy1147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                            (show (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from
                              (by
                                unfold nb078AlphaDummy1148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                            ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                            ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                            ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
                            ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
                            ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                            ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                            ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
                            ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                              unfold nb078AlphaDummy1147;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                          (show (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from (by
                              unfold nb078AlphaDummy1148;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                                unfold nb078AlphaDummy1147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                            (show (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from
                              (by
                                unfold nb078AlphaDummy1148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                            ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                            ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                            ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
                            ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
                            ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                            ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                            ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
                            ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1143) from (by
                        unfold nb078AlphaDummy1143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                    (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1145 h) from (by
                        unfold nb078AlphaDummy1145;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1187 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1144) from (by
                          unfold nb078AlphaDummy1144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1186) 1))))
                      (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1146 h) from (by
                          unfold nb078AlphaDummy1146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1187 h) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1169) from (by
                            unfold nb078AlphaDummy1169;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1216) 0))))
                        (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1170 h) from (by
                            unfold nb078AlphaDummy1170;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1217 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1136) ≠ (nb078AlphaDummy1167) from (by
                              unfold nb078AlphaDummy1167;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1214) 0))))
                          (show (nb078AlphaDummy1138 h) ≠ (nb078AlphaDummy1168 h) from (by
                              unfold nb078AlphaDummy1168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1215 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1136))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1138 h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb078AlphaDummy1143) ≠
        (nb078AlphaDummy1150) from (by
                                          unfold nb078AlphaDummy1150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1190)
                                                  1)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1153 h) from (by
                                          unfold nb078AlphaDummy1153;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1191 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1143) ≠
        (nb078AlphaDummy1149) from (by
          unfold nb078AlphaDummy1149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1152 h) from (by
          unfold nb078AlphaDummy1152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
          unfold nb078AlphaDummy1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188) 0)))) (show (nb078AlphaDummy1145 h) ≠
        (nb078AlphaDummy1148 h) from (by
          unfold nb078AlphaDummy1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy1151),
        (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150), (nb078AlphaDummy1153 h)),
        ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)), ((nb078AlphaDummy1147),
        (nb078AlphaDummy1148 h)), ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
        ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)), ((nb078AlphaDummy1169),
        (nb078AlphaDummy1170 h)), ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
        ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135),
        (nb078AlphaDummy1137 h)), ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
        ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1157) from (by
          unfold
            nb078AlphaDummy1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1158 h) from (by
          unfold
            nb078AlphaDummy1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1155) from (by
          unfold
            nb078AlphaDummy1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1156 h) from (by
          unfold
            nb078AlphaDummy1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1151), (nb078AlphaDummy1154 h)), ((nb078AlphaDummy1150),
        (nb078AlphaDummy1153 h)), ((nb078AlphaDummy1149), (nb078AlphaDummy1152 h)),
        ((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)), ((nb078AlphaDummy1143),
        (nb078AlphaDummy1145 h)), ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
        ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)), ((nb078AlphaDummy1167),
        (nb078AlphaDummy1168 h)), ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
        ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)), ((nb078AlphaDummy1165),
        (nb078AlphaDummy1166 h)), ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129),
        (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1150) ≠ (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1161) from (by
          unfold
            nb078AlphaDummy1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1162 h) from (by
          unfold
            nb078AlphaDummy1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1150) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078AlphaDummy1153 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1151) ≠ (nb078AlphaDummy1163) from (by
          unfold
            nb078AlphaDummy1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1164 h) from (by
          unfold
            nb078AlphaDummy1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1151) ≠
        (nb078AlphaDummy1159) from (by
          unfold
            nb078AlphaDummy1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078AlphaDummy1154 h) ≠ (nb078AlphaDummy1160 h) from (by
          unfold
            nb078AlphaDummy1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                                  unfold nb078AlphaDummy1147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1188) 0)))) (show
                                (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from (by
                                  unfold nb078AlphaDummy1148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                              ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                              ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                              ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
                              ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
                              ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                              ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                              ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
                              ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                                unfold nb078AlphaDummy1147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                            (show (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from
                              (by
                                unfold nb078AlphaDummy1148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy1143) ≠ (nb078AlphaDummy1147) from (by
                                  unfold nb078AlphaDummy1147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1188) 0)))) (show
                                (nb078AlphaDummy1145 h) ≠ (nb078AlphaDummy1148 h) from (by
                                  unfold nb078AlphaDummy1148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy1147), (nb078AlphaDummy1148 h)),
                              ((nb078AlphaDummy1143), (nb078AlphaDummy1145 h)),
                              ((nb078AlphaDummy1144), (nb078AlphaDummy1146 h)),
                              ((nb078AlphaDummy1169), (nb078AlphaDummy1170 h)),
                              ((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)),
                              ((nb078AlphaDummy1136), (nb078AlphaDummy1138 h)),
                              ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
                              ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)),
                              ((nb078AlphaDummy1139), (nb078AlphaDummy1140 h)),
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                              ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
