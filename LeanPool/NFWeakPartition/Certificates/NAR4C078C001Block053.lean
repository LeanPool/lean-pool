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

@[expose]
noncomputable def nb078_split_alpha_0137 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
        ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
        ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
        ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1127))
          (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1127))
            (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1128 h))
          (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1128 h))
            (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1101) from
                    (by
                      unfold nb078_alpha_dummy_1101;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                  (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1103 h) from (by
                      unfold nb078_alpha_dummy_1103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1145 h) 0))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1102) from (by
                        unfold nb078_alpha_dummy_1102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 1))))
                    (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1104 h) from (by
                        unfold nb078_alpha_dummy_1104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1145 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1127) from (by
                          unfold nb078_alpha_dummy_1127;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1174) 0))))
                      (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1128 h) from (by
                          unfold nb078_alpha_dummy_1128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1175 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1125) from (by
                            unfold nb078_alpha_dummy_1125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1172) 0))))
                        (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1126 h) from (by
                            unfold nb078_alpha_dummy_1126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1173 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1108) from
                                      (by
                                        unfold nb078_alpha_dummy_1108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1148)
                                                1)))) (show (nb078_alpha_dummy_1103 h) ≠
                                        (nb078_alpha_dummy_1111 h) from (by
                                        unfold nb078_alpha_dummy_1111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1149 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1107) from
                                        (by
                                          unfold nb078_alpha_dummy_1107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1148)
                                                  0)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1110 h) from (by
                                          unfold nb078_alpha_dummy_1110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1149 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1101) ≠
        (nb078_alpha_dummy_1105) from (by
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
                  (nb078_support_mem_1147 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1109),
        (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)),
                                        ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)),
                                        ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                                        ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                                        ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                                        ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
                                        ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
                                        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                                        ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                                        ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
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
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1115) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                        [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)),
        ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107),
        (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
        ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102),
        (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
        ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094),
        (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
        ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097),
        (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                                unfold nb078_alpha_dummy_1105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                            (show (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from
                              (by
                                unfold nb078_alpha_dummy_1106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                            ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                            ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                            ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
                            ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
                            ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                            ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                            ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
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
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                              unfold nb078_alpha_dummy_1105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                          (show (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from (by
                              unfold nb078_alpha_dummy_1106;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                                unfold nb078_alpha_dummy_1105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                            (show (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from
                              (by
                                unfold nb078_alpha_dummy_1106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                            ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                            ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                            ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
                            ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
                            ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                            ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                            ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
                            ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1101) from (by
                        unfold nb078_alpha_dummy_1101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1144) 0))))
                    (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1103 h) from (by
                        unfold nb078_alpha_dummy_1103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1145 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1102) from (by
                          unfold nb078_alpha_dummy_1102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1144) 1))))
                      (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1104 h) from (by
                          unfold nb078_alpha_dummy_1104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1145 h) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1127) from (by
                            unfold nb078_alpha_dummy_1127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1174) 0))))
                        (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1128 h) from (by
                            unfold nb078_alpha_dummy_1128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1175 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1094) ≠ (nb078_alpha_dummy_1125) from (by
                              unfold nb078_alpha_dummy_1125;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1172) 0))))
                          (show (nb078_alpha_dummy_1096 h) ≠ (nb078_alpha_dummy_1126 h) from (by
                              unfold nb078_alpha_dummy_1126;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1173 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb078_alpha_dummy_1101) ≠
        (nb078_alpha_dummy_1108) from (by
                                          unfold nb078_alpha_dummy_1108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1148)
                                                  1)))) (show (nb078_alpha_dummy_1103 h) ≠
        (nb078_alpha_dummy_1111 h) from (by
                                          unfold nb078_alpha_dummy_1111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1149 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1101) ≠
        (nb078_alpha_dummy_1107) from (by
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
                  (nb078_support_mem_1147 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1109),
        (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)),
        ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105),
        (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
        ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1127),
        (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
        ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093),
        (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
        ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1115) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)), ((nb078_alpha_dummy_1125),
        (nb078_alpha_dummy_1126 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
        ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1123),
        (nb078_alpha_dummy_1124 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                                  unfold nb078_alpha_dummy_1105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1146) 0)))) (show
                                (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from (by
                                  unfold nb078_alpha_dummy_1106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                              ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                              ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                              ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
                              ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
                              ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                              ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                              ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                                unfold nb078_alpha_dummy_1105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1146) 0))))
                            (show (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from
                              (by
                                unfold nb078_alpha_dummy_1106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1105) from (by
                                  unfold nb078_alpha_dummy_1105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1146) 0)))) (show
                                (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1106 h) from (by
                                  unfold nb078_alpha_dummy_1106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1147 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)),
                              ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)),
                              ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)),
                              ((nb078_alpha_dummy_1127), (nb078_alpha_dummy_1128 h)),
                              ((nb078_alpha_dummy_1125), (nb078_alpha_dummy_1126 h)),
                              ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)),
                              ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)),
                              ((nb078_alpha_dummy_1123), (nb078_alpha_dummy_1124 h)),
                              ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                              ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


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

@[expose]
noncomputable def nb078_split_alpha_0138 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1141))
          (Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1141)) (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1142 h))
          (Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1142 h))
            (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1136) from
                    (by
                      unfold nb078_alpha_dummy_1136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
                  (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1138 h) from (by
                      unfold nb078_alpha_dummy_1138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 1))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1135) from (by
                        unfold nb078_alpha_dummy_1135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 0))))
                    (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1137 h) from (by
                        unfold nb078_alpha_dummy_1137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1182 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1141) from (by
                          unfold nb078_alpha_dummy_1141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1184) 0))))
                      (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1142 h) from (by
                          unfold nb078_alpha_dummy_1142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1185 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1139) from (by
                            unfold nb078_alpha_dummy_1139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1181) 0))))
                        (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1140 h) from (by
                            unfold nb078_alpha_dummy_1140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1183 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                          (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1129))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1130))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1143) from (by
                              unfold nb078_alpha_dummy_1143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                          (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1145 h) from (by
                              unfold nb078_alpha_dummy_1145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1187 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1144) from (by
                                unfold nb078_alpha_dummy_1144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1186) 1))))
                            (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1146 h) from
                              (by
                                unfold nb078_alpha_dummy_1146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1187 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1150) from (by
          unfold nb078_alpha_dummy_1150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 1)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1153 h) from (by
          unfold nb078_alpha_dummy_1153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1149) from (by
          unfold nb078_alpha_dummy_1149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1152 h) from (by
          unfold nb078_alpha_dummy_1152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
          unfold nb078_alpha_dummy_1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188) 0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1148 h) from (by
          unfold nb078_alpha_dummy_1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150),
        (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)),
        ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143),
        (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135),
        (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150),
        (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)),
        ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143),
        (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135),
        (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from
                                      (by
                                        unfold nb078_alpha_dummy_1147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1188)
                                                0)))) (show (nb078_alpha_dummy_1145 h) ≠
                                        (nb078_alpha_dummy_1148 h) from (by
                                        unfold nb078_alpha_dummy_1148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1189 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                                    ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                                    ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                                    ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                                    ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                                    ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
                                    ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                                    ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                    ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                    ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
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
                                    (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                                      unfold nb078_alpha_dummy_1147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1188)
                                              0)))) (show (nb078_alpha_dummy_1145 h) ≠
                                      (nb078_alpha_dummy_1148 h) from (by
                                      unfold nb078_alpha_dummy_1148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1189 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from
                                      (by
                                        unfold nb078_alpha_dummy_1147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1188)
                                                0)))) (show (nb078_alpha_dummy_1145 h) ≠
                                        (nb078_alpha_dummy_1148 h) from (by
                                        unfold nb078_alpha_dummy_1148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1189 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                                    ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                                    ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                                    ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                                    ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                                    ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
                                    ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                                    ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                    ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                    ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
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
                    (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1136) from (by
                        unfold nb078_alpha_dummy_1136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
                    (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1138 h) from (by
                        unfold nb078_alpha_dummy_1138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1182 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1135) from (by
                          unfold nb078_alpha_dummy_1135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1180) 0))))
                      (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1137 h) from (by
                          unfold nb078_alpha_dummy_1137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1182 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1141) from (by
                            unfold nb078_alpha_dummy_1141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1184) 0))))
                        (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1142 h) from (by
                            unfold nb078_alpha_dummy_1142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1185 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1139) from (by
                              unfold nb078_alpha_dummy_1139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1181) 0))))
                          (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1140 h) from (by
                              unfold nb078_alpha_dummy_1140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1183 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1130))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1143) from (by
                                unfold nb078_alpha_dummy_1143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                            (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1145 h) from
                              (by
                                unfold nb078_alpha_dummy_1145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1187 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1144) from (by
                                  unfold nb078_alpha_dummy_1144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1186) 1)))) (show
                                (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1146 h) from (by
                                  unfold nb078_alpha_dummy_1146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1187 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_1138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1150) from (by
          unfold nb078_alpha_dummy_1150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 1)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1153 h) from (by
          unfold nb078_alpha_dummy_1153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1149) from (by
          unfold nb078_alpha_dummy_1149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1152 h) from (by
          unfold nb078_alpha_dummy_1152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1143) ≠
        (nb078_alpha_dummy_1147) from (by
          unfold nb078_alpha_dummy_1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188)
                  0)))) (show (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from (by
          unfold nb078_alpha_dummy_1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150),
        (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)),
        ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143),
        (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135),
        (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150),
        (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)),
        ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143),
        (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135),
        (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from
                                        (by
                                          unfold nb078_alpha_dummy_1147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1188)
                                                  0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1148 h) from (by
                                          unfold nb078_alpha_dummy_1148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1189 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                                      ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                                      ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                                      ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                                      ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                                      ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
                                      ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                                      ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                      ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                      ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
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
                                      (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from
                                      (by
                                        unfold nb078_alpha_dummy_1147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1188)
                                                0)))) (show (nb078_alpha_dummy_1145 h) ≠
                                        (nb078_alpha_dummy_1148 h) from (by
                                        unfold nb078_alpha_dummy_1148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1189 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from
                                        (by
                                          unfold nb078_alpha_dummy_1147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1188)
                                                  0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1148 h) from (by
                                          unfold nb078_alpha_dummy_1148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1189 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                                      ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                                      ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                                      ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                                      ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                                      ((nb078_alpha_dummy_1141), (nb078_alpha_dummy_1142 h)),
                                      ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                                      ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                      ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                      ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
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

@[expose]
noncomputable def nb078_split_alpha_0139 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
        ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
        ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
        ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1169))
          (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1169))
            (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1170 h))
          (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1170 h))
            (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1143) from
                    (by
                      unfold nb078_alpha_dummy_1143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                  (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1145 h) from (by
                      unfold nb078_alpha_dummy_1145;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1187 h) 0))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1144) from (by
                        unfold nb078_alpha_dummy_1144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 1))))
                    (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1146 h) from (by
                        unfold nb078_alpha_dummy_1146;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1187 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1169) from (by
                          unfold nb078_alpha_dummy_1169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1216) 0))))
                      (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1170 h) from (by
                          unfold nb078_alpha_dummy_1170;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1217 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1167) from (by
                            unfold nb078_alpha_dummy_1167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1214) 0))))
                        (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1168 h) from (by
                            unfold nb078_alpha_dummy_1168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1215 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1150) from
                                      (by
                                        unfold nb078_alpha_dummy_1150;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1190)
                                                1)))) (show (nb078_alpha_dummy_1145 h) ≠
                                        (nb078_alpha_dummy_1153 h) from (by
                                        unfold nb078_alpha_dummy_1153;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1191 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1149) from
                                        (by
                                          unfold nb078_alpha_dummy_1149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1190)
                                                  0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1152 h) from (by
                                          unfold nb078_alpha_dummy_1152;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1191 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1143) ≠
        (nb078_alpha_dummy_1147) from (by
          unfold nb078_alpha_dummy_1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188) 0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1148 h) from (by
          unfold nb078_alpha_dummy_1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1151),
        (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)),
                                        ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)),
                                        ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                                        ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                                        ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                                        ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
                                        ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
                                        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                                        ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                                        ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
                                        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                                        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                        ((nb078_alpha_dummy_002), h),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)),
        ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149),
        (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
        ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144),
        (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
        ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136),
        (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
        ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139),
        (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                                unfold nb078_alpha_dummy_1147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                            (show (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from
                              (by
                                unfold nb078_alpha_dummy_1148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                            ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                            ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                            ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
                            ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
                            ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                            ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                            ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
                            ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                            ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                            ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                            ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                              unfold nb078_alpha_dummy_1147;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                          (show (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from (by
                              unfold nb078_alpha_dummy_1148;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                                unfold nb078_alpha_dummy_1147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                            (show (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from
                              (by
                                unfold nb078_alpha_dummy_1148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                            ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                            ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                            ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
                            ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
                            ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                            ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                            ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
                            ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                            ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                            ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                            ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1143) from (by
                        unfold nb078_alpha_dummy_1143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1186) 0))))
                    (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1145 h) from (by
                        unfold nb078_alpha_dummy_1145;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1187 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1144) from (by
                          unfold nb078_alpha_dummy_1144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1186) 1))))
                      (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1146 h) from (by
                          unfold nb078_alpha_dummy_1146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1187 h) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1169) from (by
                            unfold nb078_alpha_dummy_1169;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1216) 0))))
                        (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1170 h) from (by
                            unfold nb078_alpha_dummy_1170;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1217 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1136) ≠ (nb078_alpha_dummy_1167) from (by
                              unfold nb078_alpha_dummy_1167;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1214) 0))))
                          (show (nb078_alpha_dummy_1138 h) ≠ (nb078_alpha_dummy_1168 h) from (by
                              unfold nb078_alpha_dummy_1168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1215 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb078_alpha_dummy_1143) ≠
        (nb078_alpha_dummy_1150) from (by
                                          unfold nb078_alpha_dummy_1150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1190)
                                                  1)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1153 h) from (by
                                          unfold nb078_alpha_dummy_1153;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1191 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1143) ≠
        (nb078_alpha_dummy_1149) from (by
          unfold nb078_alpha_dummy_1149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1190) 0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1152 h) from (by
          unfold nb078_alpha_dummy_1152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1191 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
          unfold nb078_alpha_dummy_1147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1188) 0)))) (show (nb078_alpha_dummy_1145 h) ≠
        (nb078_alpha_dummy_1148 h) from (by
          unfold nb078_alpha_dummy_1148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1189 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1151),
        (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150), (nb078_alpha_dummy_1153 h)),
        ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)), ((nb078_alpha_dummy_1147),
        (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
        ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)), ((nb078_alpha_dummy_1169),
        (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
        ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)), ((nb078_alpha_dummy_1135),
        (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
        ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1194)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1195
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1192)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1193
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1157) from (by
          unfold
            nb078_alpha_dummy_1157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1198)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1158 h) from (by
          unfold
            nb078_alpha_dummy_1158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1199
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1155) from (by
          unfold
            nb078_alpha_dummy_1155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1196)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1156 h) from (by
          unfold
            nb078_alpha_dummy_1156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1197
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1151), (nb078_alpha_dummy_1154 h)), ((nb078_alpha_dummy_1150),
        (nb078_alpha_dummy_1153 h)), ((nb078_alpha_dummy_1149), (nb078_alpha_dummy_1152 h)),
        ((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)), ((nb078_alpha_dummy_1143),
        (nb078_alpha_dummy_1145 h)), ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
        ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)), ((nb078_alpha_dummy_1167),
        (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
        ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165),
        (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1161) from (by
          unfold
            nb078_alpha_dummy_1161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1202)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1162 h) from (by
          unfold
            nb078_alpha_dummy_1162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1203
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1150) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1200)
                  0)))) (show (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1201
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1151) ≠ (nb078_alpha_dummy_1163) from (by
          unfold
            nb078_alpha_dummy_1163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1206)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1164 h) from (by
          unfold
            nb078_alpha_dummy_1164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1207
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1151) ≠
        (nb078_alpha_dummy_1159) from (by
          unfold
            nb078_alpha_dummy_1159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1204)
                  0)))) (show (nb078_alpha_dummy_1154 h) ≠ (nb078_alpha_dummy_1160 h) from (by
          unfold
            nb078_alpha_dummy_1160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1205
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                                  unfold nb078_alpha_dummy_1147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1188) 0)))) (show
                                (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from (by
                                  unfold nb078_alpha_dummy_1148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                              ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                              ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                              ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
                              ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
                              ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                              ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                              ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
                              ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                              ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                              ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                              ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                                unfold nb078_alpha_dummy_1147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1188) 0))))
                            (show (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from
                              (by
                                unfold nb078_alpha_dummy_1148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1147) from (by
                                  unfold nb078_alpha_dummy_1147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1188) 0)))) (show
                                (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1148 h) from (by
                                  unfold nb078_alpha_dummy_1148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1189 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_1147), (nb078_alpha_dummy_1148 h)),
                              ((nb078_alpha_dummy_1143), (nb078_alpha_dummy_1145 h)),
                              ((nb078_alpha_dummy_1144), (nb078_alpha_dummy_1146 h)),
                              ((nb078_alpha_dummy_1169), (nb078_alpha_dummy_1170 h)),
                              ((nb078_alpha_dummy_1167), (nb078_alpha_dummy_1168 h)),
                              ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
                              ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)),
                              ((nb078_alpha_dummy_1165), (nb078_alpha_dummy_1166 h)),
                              ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
                              ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                              ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                              ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                              ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
