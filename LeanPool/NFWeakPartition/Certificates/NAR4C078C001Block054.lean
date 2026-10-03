/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block053

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part160`. -/


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
noncomputable def nb078_split_alpha_0140 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1177))
          (Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1177)) (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1178 h))
          (Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1178 h))
            (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1172) from
                    (by
                      unfold nb078_alpha_dummy_1172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
                  (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1174 h) from (by
                      unfold nb078_alpha_dummy_1174;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 1))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1171) from (by
                        unfold nb078_alpha_dummy_1171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 0))))
                    (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1173 h) from (by
                        unfold nb078_alpha_dummy_1173;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1220 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1177) from (by
                          unfold nb078_alpha_dummy_1177;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1222) 0))))
                      (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1178 h) from (by
                          unfold nb078_alpha_dummy_1178;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1223 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1175) from (by
                            unfold nb078_alpha_dummy_1175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1219) 0))))
                        (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1176 h) from (by
                            unfold nb078_alpha_dummy_1176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1221 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1130))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1129))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1131 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1179) from (by
                              unfold nb078_alpha_dummy_1179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                          (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1181 h) from (by
                              unfold nb078_alpha_dummy_1181;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1225 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1180) from (by
                                unfold nb078_alpha_dummy_1180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1224) 1))))
                            (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1182 h) from
                              (by
                                unfold nb078_alpha_dummy_1182;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1225 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1172))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1174 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1186) from (by
          unfold nb078_alpha_dummy_1186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 1)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1189 h) from (by
          unfold nb078_alpha_dummy_1189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1185) from (by
          unfold nb078_alpha_dummy_1185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1188 h) from (by
          unfold nb078_alpha_dummy_1188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
          unfold nb078_alpha_dummy_1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226) 0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1184 h) from (by
          unfold nb078_alpha_dummy_1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186),
        (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)),
        ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179),
        (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171),
        (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130),
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
        (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186),
        (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)),
        ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179),
        (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171),
        (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from
                                      (by
                                        unfold nb078_alpha_dummy_1183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1226)
                                                0)))) (show (nb078_alpha_dummy_1181 h) ≠
                                        (nb078_alpha_dummy_1184 h) from (by
                                        unfold nb078_alpha_dummy_1184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1227 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                                    ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                                    ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                                    ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                                    ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                                    ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
                                    ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
                                    (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                                      unfold nb078_alpha_dummy_1183;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1226)
                                              0)))) (show (nb078_alpha_dummy_1181 h) ≠
                                      (nb078_alpha_dummy_1184 h) from (by
                                      unfold nb078_alpha_dummy_1184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1227 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from
                                      (by
                                        unfold nb078_alpha_dummy_1183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1226)
                                                0)))) (show (nb078_alpha_dummy_1181 h) ≠
                                        (nb078_alpha_dummy_1184 h) from (by
                                        unfold nb078_alpha_dummy_1184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1227 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                                    ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                                    ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                                    ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                                    ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                                    ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
                                    ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
                    (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1172) from (by
                        unfold nb078_alpha_dummy_1172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
                    (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1174 h) from (by
                        unfold nb078_alpha_dummy_1174;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1220 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1171) from (by
                          unfold nb078_alpha_dummy_1171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1218) 0))))
                      (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1173 h) from (by
                          unfold nb078_alpha_dummy_1173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1220 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1177) from (by
                            unfold nb078_alpha_dummy_1177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1222) 0))))
                        (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1178 h) from (by
                            unfold nb078_alpha_dummy_1178;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1223 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1175) from (by
                              unfold nb078_alpha_dummy_1175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1219) 0))))
                          (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1176 h) from (by
                              unfold nb078_alpha_dummy_1176;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1221 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1129))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1179) from (by
                                unfold nb078_alpha_dummy_1179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                            (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1181 h) from
                              (by
                                unfold nb078_alpha_dummy_1181;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1225 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1180) from (by
                                  unfold nb078_alpha_dummy_1180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1224) 1)))) (show
                                (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1182 h) from (by
                                  unfold nb078_alpha_dummy_1182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1225 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_1172))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_1174 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1186) from (by
          unfold nb078_alpha_dummy_1186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 1)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1189 h) from (by
          unfold nb078_alpha_dummy_1189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1185) from (by
          unfold nb078_alpha_dummy_1185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1188 h) from (by
          unfold nb078_alpha_dummy_1188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1179) ≠
        (nb078_alpha_dummy_1183) from (by
          unfold nb078_alpha_dummy_1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226)
                  0)))) (show (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from (by
          unfold nb078_alpha_dummy_1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186),
        (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)),
        ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179),
        (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171),
        (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130),
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
        (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186),
        (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)),
        ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179),
        (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171),
        (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from
                                        (by
                                          unfold nb078_alpha_dummy_1183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1226)
                                                  0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1184 h) from (by
                                          unfold nb078_alpha_dummy_1184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1227 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                                      ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                                      ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                                      ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                                      ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                                      ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
                                      ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
                                      (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from
                                      (by
                                        unfold nb078_alpha_dummy_1183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1226)
                                                0)))) (show (nb078_alpha_dummy_1181 h) ≠
                                        (nb078_alpha_dummy_1184 h) from (by
                                        unfold nb078_alpha_dummy_1184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1227 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from
                                        (by
                                          unfold nb078_alpha_dummy_1183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1226)
                                                  0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1184 h) from (by
                                          unfold nb078_alpha_dummy_1184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1227 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                                      ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                                      ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                                      ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                                      ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                                      ((nb078_alpha_dummy_1177), (nb078_alpha_dummy_1178 h)),
                                      ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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

/-! Certificates from `NAR4C078C001Part161`. -/


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
noncomputable def nb078_split_alpha_0141 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
        ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
        ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
        ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1205))
          (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1205))
            (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1206 h))
          (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1206 h))
            (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1179) from
                    (by
                      unfold nb078_alpha_dummy_1179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                  (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1181 h) from (by
                      unfold nb078_alpha_dummy_1181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1225 h) 0))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1180) from (by
                        unfold nb078_alpha_dummy_1180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1224) 1))))
                    (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1182 h) from (by
                        unfold nb078_alpha_dummy_1182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1225 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1205) from (by
                          unfold nb078_alpha_dummy_1205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1254) 0))))
                      (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1206 h) from (by
                          unfold nb078_alpha_dummy_1206;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1255 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1203) from (by
                            unfold nb078_alpha_dummy_1203;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1252) 0))))
                        (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1204 h) from (by
                            unfold nb078_alpha_dummy_1204;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1253 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1172))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_1174 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1186) from
                                      (by
                                        unfold nb078_alpha_dummy_1186;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1228)
                                                1)))) (show (nb078_alpha_dummy_1181 h) ≠
                                        (nb078_alpha_dummy_1189 h) from (by
                                        unfold nb078_alpha_dummy_1189;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1229 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1185) from
                                        (by
                                          unfold nb078_alpha_dummy_1185;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1228)
                                                  0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1188 h) from (by
                                          unfold nb078_alpha_dummy_1188;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1229 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1179) ≠
        (nb078_alpha_dummy_1183) from (by
          unfold nb078_alpha_dummy_1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226) 0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1184 h) from (by
          unfold nb078_alpha_dummy_1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1187),
        (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)),
                                        ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)),
                                        ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                                        ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                                        ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                                        ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
                                        ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
                                        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                                        ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                                        ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
                                        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
        (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)),
        ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185),
        (nb078_alpha_dummy_1188 h)), ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
        ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180),
        (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
        ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)), ((nb078_alpha_dummy_1172),
        (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
        ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)), ((nb078_alpha_dummy_1175),
        (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                                unfold nb078_alpha_dummy_1183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                            (show (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from
                              (by
                                unfold nb078_alpha_dummy_1184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                            ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                            ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                            ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
                            ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
                            ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                            ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                            ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
                            ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
                          (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                              unfold nb078_alpha_dummy_1183;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                          (show (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from (by
                              unfold nb078_alpha_dummy_1184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                                unfold nb078_alpha_dummy_1183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                            (show (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from
                              (by
                                unfold nb078_alpha_dummy_1184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                            ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                            ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                            ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
                            ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
                            ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                            ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                            ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
                            ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
                    (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1179) from (by
                        unfold nb078_alpha_dummy_1179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                    (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1181 h) from (by
                        unfold nb078_alpha_dummy_1181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1225 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1180) from (by
                          unfold nb078_alpha_dummy_1180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1224) 1))))
                      (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1182 h) from (by
                          unfold nb078_alpha_dummy_1182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1225 h) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1205) from (by
                            unfold nb078_alpha_dummy_1205;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1254) 0))))
                        (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1206 h) from (by
                            unfold nb078_alpha_dummy_1206;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1255 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1172) ≠ (nb078_alpha_dummy_1203) from (by
                              unfold nb078_alpha_dummy_1203;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1252) 0))))
                          (show (nb078_alpha_dummy_1174 h) ≠ (nb078_alpha_dummy_1204 h) from (by
                              unfold nb078_alpha_dummy_1204;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1253 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1172))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1174 h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb078_alpha_dummy_1179) ≠
        (nb078_alpha_dummy_1186) from (by
                                          unfold nb078_alpha_dummy_1186;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1228)
                                                  1)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1189 h) from (by
                                          unfold nb078_alpha_dummy_1189;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1229 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1179) ≠
        (nb078_alpha_dummy_1185) from (by
          unfold nb078_alpha_dummy_1185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1188 h) from (by
          unfold nb078_alpha_dummy_1188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
          unfold nb078_alpha_dummy_1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226) 0)))) (show (nb078_alpha_dummy_1181 h) ≠
        (nb078_alpha_dummy_1184 h) from (by
          unfold nb078_alpha_dummy_1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1187),
        (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186), (nb078_alpha_dummy_1189 h)),
        ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)), ((nb078_alpha_dummy_1183),
        (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
        ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)), ((nb078_alpha_dummy_1205),
        (nb078_alpha_dummy_1206 h)), ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
        ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)), ((nb078_alpha_dummy_1171),
        (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
        ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)), ((nb078_alpha_dummy_1130),
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
        (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1193) from (by
          unfold
            nb078_alpha_dummy_1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1194 h) from (by
          unfold
            nb078_alpha_dummy_1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1191) from (by
          unfold
            nb078_alpha_dummy_1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1192 h) from (by
          unfold
            nb078_alpha_dummy_1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1187), (nb078_alpha_dummy_1190 h)), ((nb078_alpha_dummy_1186),
        (nb078_alpha_dummy_1189 h)), ((nb078_alpha_dummy_1185), (nb078_alpha_dummy_1188 h)),
        ((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)), ((nb078_alpha_dummy_1179),
        (nb078_alpha_dummy_1181 h)), ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
        ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)), ((nb078_alpha_dummy_1203),
        (nb078_alpha_dummy_1204 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
        ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1201),
        (nb078_alpha_dummy_1202 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1197) from (by
          unfold
            nb078_alpha_dummy_1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1198 h) from (by
          unfold
            nb078_alpha_dummy_1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1186) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1187) ≠ (nb078_alpha_dummy_1199) from (by
          unfold
            nb078_alpha_dummy_1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1200 h) from (by
          unfold
            nb078_alpha_dummy_1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1187) ≠
        (nb078_alpha_dummy_1195) from (by
          unfold
            nb078_alpha_dummy_1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078_alpha_dummy_1190 h) ≠ (nb078_alpha_dummy_1196 h) from (by
          unfold
            nb078_alpha_dummy_1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                                  unfold nb078_alpha_dummy_1183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1226) 0)))) (show
                                (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from (by
                                  unfold nb078_alpha_dummy_1184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                              ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                              ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                              ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
                              ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
                              ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                              ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                              ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
                              ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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
                            (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                                unfold nb078_alpha_dummy_1183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                            (show (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from
                              (by
                                unfold nb078_alpha_dummy_1184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1183) from (by
                                  unfold nb078_alpha_dummy_1183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1226) 0)))) (show
                                (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1184 h) from (by
                                  unfold nb078_alpha_dummy_1184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_1183), (nb078_alpha_dummy_1184 h)),
                              ((nb078_alpha_dummy_1179), (nb078_alpha_dummy_1181 h)),
                              ((nb078_alpha_dummy_1180), (nb078_alpha_dummy_1182 h)),
                              ((nb078_alpha_dummy_1205), (nb078_alpha_dummy_1206 h)),
                              ((nb078_alpha_dummy_1203), (nb078_alpha_dummy_1204 h)),
                              ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
                              ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)),
                              ((nb078_alpha_dummy_1201), (nb078_alpha_dummy_1202 h)),
                              ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
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

/-! Certificates from `NAR4C078C001Part162`. -/


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
noncomputable def nb078_split_alpha_0142 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_859))
          (Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_859)) (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_860 h))
          (Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_860 h))
            (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_854) from
                    (by
                      unfold nb078_alpha_dummy_854;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                  (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_856 h) from (by
                      unfold nb078_alpha_dummy_856;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_853) from
                      (by
                        unfold nb078_alpha_dummy_853;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                    (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_855 h) from (by
                        unfold nb078_alpha_dummy_855;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_859) from (by
                          unfold nb078_alpha_dummy_859;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_860 h) from (by
                          unfold nb078_alpha_dummy_860;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_857) from (by
                            unfold nb078_alpha_dummy_857;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_858 h) from (by
                            unfold nb078_alpha_dummy_858;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from (by
                              unfold nb078_alpha_dummy_861;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                          (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                              unfold nb078_alpha_dummy_863;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from (by
                                unfold nb078_alpha_dummy_862;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                            (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from (by
                                unfold nb078_alpha_dummy_864;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from (by
          unfold nb078_alpha_dummy_868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_871 h) from (by
          unfold nb078_alpha_dummy_871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_867) from (by
          unfold nb078_alpha_dummy_867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
          unfold nb078_alpha_dummy_870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
          unfold nb078_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
          unfold nb078_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
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
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_879) from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879)
        from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠
        (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                        unfold nb078_alpha_dummy_865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_866 h) from (by
                                        unfold nb078_alpha_dummy_866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                    ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                    ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                    ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                    ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                    ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                    ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
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
                                  (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from
                                    (by
                                      unfold nb078_alpha_dummy_865;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0890)
                                              0)))) (show
                                    (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from
                                    (by
                                      unfold nb078_alpha_dummy_866;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0891 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                        unfold nb078_alpha_dummy_865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_866 h) from (by
                                        unfold nb078_alpha_dummy_866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                    ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                    ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                    ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                    ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                    ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                    ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
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
                  (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_854) from
                      (by
                        unfold nb078_alpha_dummy_854;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                    (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_856 h) from (by
                        unfold nb078_alpha_dummy_856;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_853) from (by
                          unfold nb078_alpha_dummy_853;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_855 h) from (by
                          unfold nb078_alpha_dummy_855;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_859) from (by
                            unfold nb078_alpha_dummy_859;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_860 h) from (by
                            unfold nb078_alpha_dummy_860;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_857) from (by
                              unfold nb078_alpha_dummy_857;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                          (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_858 h) from (by
                              unfold nb078_alpha_dummy_858;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv)
                              (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_847))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from (by
                                unfold nb078_alpha_dummy_861;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                            (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                                unfold nb078_alpha_dummy_863;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from (by
                                  unfold nb078_alpha_dummy_862;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                              (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from
                                (by
                                  unfold nb078_alpha_dummy_864;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_856 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from (by
          unfold nb078_alpha_dummy_868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_871 h) from (by
          unfold nb078_alpha_dummy_871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_867) from (by
          unfold nb078_alpha_dummy_867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
          unfold nb078_alpha_dummy_870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865)
        from (by
          unfold nb078_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890)
                  0)))) (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
          unfold nb078_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
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
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_879) from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879)
        from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠
        (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from
                                        (by
                                          unfold nb078_alpha_dummy_865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
                                          unfold nb078_alpha_dummy_866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                      ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                      ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                      ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                      ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                      ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                      ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
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
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                        unfold nb078_alpha_dummy_865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_866 h) from (by
                                        unfold nb078_alpha_dummy_866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from
                                        (by
                                          unfold nb078_alpha_dummy_865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
                                          unfold nb078_alpha_dummy_866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                      ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                      ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                      ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                      ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                      ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                      ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
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
