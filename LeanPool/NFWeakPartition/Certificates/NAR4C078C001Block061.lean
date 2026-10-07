/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block060

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part178`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0160`. -/
@[expose]
noncomputable def nb078SplitAlpha0160 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1177))
          (Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1177)) (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCphi (Class.cv (nb078AlphaDummy1172)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1178 h))
          (Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1178 h))
            (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCphi (Class.cv (nb078AlphaDummy1174 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1172) from
                    (by
                      unfold nb078AlphaDummy1172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
                  (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1174 h) from (by
                      unfold nb078AlphaDummy1174;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 1))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1171) from (by
                        unfold nb078AlphaDummy1171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 0))))
                    (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1173 h) from (by
                        unfold nb078AlphaDummy1173;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1220 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1177) from (by
                          unfold nb078AlphaDummy1177;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1222) 0))))
                      (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1178 h) from (by
                          unfold nb078AlphaDummy1178;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1223 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1175) from (by
                            unfold nb078AlphaDummy1175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1219) 0))))
                        (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1176 h) from (by
                            unfold nb078AlphaDummy1176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1221 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1130))).fv ∪
                      ((Class.cv (nb078AlphaDummy1129))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy1131 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1179) from (by
                              unfold nb078AlphaDummy1179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                          (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1181 h) from (by
                              unfold nb078AlphaDummy1181;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1225 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1180) from (by
                                unfold nb078AlphaDummy1180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1224) 1))))
                            (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1182 h) from
                              (by
                                unfold nb078AlphaDummy1182;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1225 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1172))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1174 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1186) from (by
          unfold nb078AlphaDummy1186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 1)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1189 h) from (by
          unfold nb078AlphaDummy1189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1185) from (by
          unfold nb078AlphaDummy1185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1188 h) from (by
          unfold nb078AlphaDummy1188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
          unfold nb078AlphaDummy1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226) 0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1184 h) from (by
          unfold nb078AlphaDummy1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1187), (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186),
        (nb078AlphaDummy1189 h)), ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)),
        ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)), ((nb078AlphaDummy1179),
        (nb078AlphaDummy1181 h)), ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171),
        (nb078AlphaDummy1173 h)), ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1187), (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186),
        (nb078AlphaDummy1189 h)), ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)),
        ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)), ((nb078AlphaDummy1179),
        (nb078AlphaDummy1181 h)), ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171),
        (nb078AlphaDummy1173 h)), ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1181
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from
                                      (by
                                        unfold nb078AlphaDummy1183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1226)
                                                0)))) (show (nb078AlphaDummy1181 h) ≠
                                        (nb078AlphaDummy1184 h) from (by
                                        unfold nb078AlphaDummy1184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1227 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                                    ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                                    ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                                    ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                                    ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                                    ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
                                    ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                                      unfold nb078AlphaDummy1183;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1226)
                                              0)))) (show (nb078AlphaDummy1181 h) ≠
                                      (nb078AlphaDummy1184 h) from (by
                                      unfold nb078AlphaDummy1184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1227 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from
                                      (by
                                        unfold nb078AlphaDummy1183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1226)
                                                0)))) (show (nb078AlphaDummy1181 h) ≠
                                        (nb078AlphaDummy1184 h) from (by
                                        unfold nb078AlphaDummy1184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1227 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                                    ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                                    ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                                    ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                                    ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                                    ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
                                    ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1172) from (by
                        unfold nb078AlphaDummy1172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
                    (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1174 h) from (by
                        unfold nb078AlphaDummy1174;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1220 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1171) from (by
                          unfold nb078AlphaDummy1171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1218) 0))))
                      (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1173 h) from (by
                          unfold nb078AlphaDummy1173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1220 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1177) from (by
                            unfold nb078AlphaDummy1177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1222) 0))))
                        (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1178 h) from (by
                            unfold nb078AlphaDummy1178;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1223 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1175) from (by
                              unfold nb078AlphaDummy1175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1219) 0))))
                          (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1176 h) from (by
                              unfold nb078AlphaDummy1176;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1221 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy1130))).fv ∪
                        ((Class.cv (nb078AlphaDummy1129))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy1131 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1179) from (by
                                unfold nb078AlphaDummy1179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                            (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1181 h) from
                              (by
                                unfold nb078AlphaDummy1181;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1225 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1180) from (by
                                  unfold nb078AlphaDummy1180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1224) 1)))) (show
                                (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1182 h) from (by
                                  unfold nb078AlphaDummy1182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1225 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy1172))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy1174 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1186) from (by
          unfold nb078AlphaDummy1186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 1)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1189 h) from (by
          unfold nb078AlphaDummy1189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1185) from (by
          unfold nb078AlphaDummy1185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1188 h) from (by
          unfold nb078AlphaDummy1188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1179) ≠
        (nb078AlphaDummy1183) from (by
          unfold nb078AlphaDummy1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226)
                  0)))) (show (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from (by
          unfold nb078AlphaDummy1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1187), (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186),
        (nb078AlphaDummy1189 h)), ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)),
        ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)), ((nb078AlphaDummy1179),
        (nb078AlphaDummy1181 h)), ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171),
        (nb078AlphaDummy1173 h)), ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1187), (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186),
        (nb078AlphaDummy1189 h)), ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)),
        ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)), ((nb078AlphaDummy1179),
        (nb078AlphaDummy1181 h)), ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171),
        (nb078AlphaDummy1173 h)), ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1181
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from
                                        (by
                                          unfold nb078AlphaDummy1183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1226)
                                                  0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1184 h) from (by
                                          unfold nb078AlphaDummy1184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1227 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                                      ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                                      ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                                      ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                                      ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                                      ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
                                      ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from
                                      (by
                                        unfold nb078AlphaDummy1183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1226)
                                                0)))) (show (nb078AlphaDummy1181 h) ≠
                                        (nb078AlphaDummy1184 h) from (by
                                        unfold nb078AlphaDummy1184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1227 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from
                                        (by
                                          unfold nb078AlphaDummy1183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1226)
                                                  0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1184 h) from (by
                                          unfold nb078AlphaDummy1184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1227 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                                      ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                                      ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                                      ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                                      ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                                      ((nb078AlphaDummy1177), (nb078AlphaDummy1178 h)),
                                      ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part179`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0161`. -/
@[expose]
noncomputable def nb078SplitAlpha0161 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
        ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
        ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
        ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1205))
          (synCphi (Class.cv (nb078AlphaDummy1172)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1205))
            (synCphi (Class.cv (nb078AlphaDummy1172))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1206 h))
          (synCphi (Class.cv (nb078AlphaDummy1174 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1206 h))
            (synCphi (Class.cv (nb078AlphaDummy1174 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1179) from
                    (by
                      unfold nb078AlphaDummy1179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                  (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1181 h) from (by
                      unfold nb078AlphaDummy1181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1225 h) 0))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1180) from (by
                        unfold nb078AlphaDummy1180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1224) 1))))
                    (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1182 h) from (by
                        unfold nb078AlphaDummy1182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1225 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1205) from (by
                          unfold nb078AlphaDummy1205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1254) 0))))
                      (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1206 h) from (by
                          unfold nb078AlphaDummy1206;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1255 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1203) from (by
                            unfold nb078AlphaDummy1203;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1252) 0))))
                        (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1204 h) from (by
                            unfold nb078AlphaDummy1204;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1253 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1172))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb078AlphaDummy1174 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1186) from
                                      (by
                                        unfold nb078AlphaDummy1186;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1228)
                                                1)))) (show (nb078AlphaDummy1181 h) ≠
                                        (nb078AlphaDummy1189 h) from (by
                                        unfold nb078AlphaDummy1189;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1229 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1185) from
                                        (by
                                          unfold nb078AlphaDummy1185;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1228)
                                                  0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1188 h) from (by
                                          unfold nb078AlphaDummy1188;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1229 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1179) ≠
        (nb078AlphaDummy1183) from (by
          unfold nb078AlphaDummy1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226) 0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1184 h) from (by
          unfold nb078AlphaDummy1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy1187),
        (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186), (nb078AlphaDummy1189 h)),
                                        ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)),
                                        ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                                        ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                                        ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                                        ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
                                        ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
                                        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                                        ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                                        ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
                                        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                                        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                        ((nb078AlphaDummy002), h),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy1187), (nb078AlphaDummy1190 h)),
        ((nb078AlphaDummy1186), (nb078AlphaDummy1189 h)), ((nb078AlphaDummy1185),
        (nb078AlphaDummy1188 h)), ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
        ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)), ((nb078AlphaDummy1180),
        (nb078AlphaDummy1182 h)), ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
        ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)), ((nb078AlphaDummy1172),
        (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
        ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)), ((nb078AlphaDummy1175),
        (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                                unfold nb078AlphaDummy1183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                            (show (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from
                              (by
                                unfold nb078AlphaDummy1184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                            ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                            ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                            ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
                            ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
                            ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                            ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                            ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
                            ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                              unfold nb078AlphaDummy1183;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                          (show (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from (by
                              unfold nb078AlphaDummy1184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                                unfold nb078AlphaDummy1183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                            (show (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from
                              (by
                                unfold nb078AlphaDummy1184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                            ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                            ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                            ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
                            ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
                            ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                            ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                            ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
                            ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1179) from (by
                        unfold nb078AlphaDummy1179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1224) 0))))
                    (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1181 h) from (by
                        unfold nb078AlphaDummy1181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1225 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1180) from (by
                          unfold nb078AlphaDummy1180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1224) 1))))
                      (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1182 h) from (by
                          unfold nb078AlphaDummy1182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1225 h) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1205) from (by
                            unfold nb078AlphaDummy1205;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1254) 0))))
                        (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1206 h) from (by
                            unfold nb078AlphaDummy1206;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1255 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1172) ≠ (nb078AlphaDummy1203) from (by
                              unfold nb078AlphaDummy1203;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1252) 0))))
                          (show (nb078AlphaDummy1174 h) ≠ (nb078AlphaDummy1204 h) from (by
                              unfold nb078AlphaDummy1204;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1253 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1172))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1174 h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb078AlphaDummy1179) ≠
        (nb078AlphaDummy1186) from (by
                                          unfold nb078AlphaDummy1186;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1228)
                                                  1)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1189 h) from (by
                                          unfold nb078AlphaDummy1189;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1229 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1179) ≠
        (nb078AlphaDummy1185) from (by
          unfold nb078AlphaDummy1185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1228) 0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1188 h) from (by
          unfold nb078AlphaDummy1188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1229 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
          unfold nb078AlphaDummy1183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1226) 0)))) (show (nb078AlphaDummy1181 h) ≠
        (nb078AlphaDummy1184 h) from (by
          unfold nb078AlphaDummy1184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1227 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy1187),
        (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186), (nb078AlphaDummy1189 h)),
        ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)), ((nb078AlphaDummy1183),
        (nb078AlphaDummy1184 h)), ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
        ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)), ((nb078AlphaDummy1205),
        (nb078AlphaDummy1206 h)), ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
        ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171),
        (nb078AlphaDummy1173 h)), ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
        ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1232)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1233
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1230)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1231
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1193) from (by
          unfold
            nb078AlphaDummy1193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1236)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1194 h) from (by
          unfold
            nb078AlphaDummy1194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1237
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1191) from (by
          unfold
            nb078AlphaDummy1191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1234)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1192 h) from (by
          unfold
            nb078AlphaDummy1192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1235
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1187), (nb078AlphaDummy1190 h)), ((nb078AlphaDummy1186),
        (nb078AlphaDummy1189 h)), ((nb078AlphaDummy1185), (nb078AlphaDummy1188 h)),
        ((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)), ((nb078AlphaDummy1179),
        (nb078AlphaDummy1181 h)), ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
        ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)), ((nb078AlphaDummy1203),
        (nb078AlphaDummy1204 h)), ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
        ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)), ((nb078AlphaDummy1201),
        (nb078AlphaDummy1202 h)), ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129),
        (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1181 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1186) ≠ (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1197) from (by
          unfold
            nb078AlphaDummy1197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1240)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1198 h) from (by
          unfold
            nb078AlphaDummy1198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1241
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1186) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1238)
                  0)))) (show (nb078AlphaDummy1189 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1239
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1187) ≠ (nb078AlphaDummy1199) from (by
          unfold
            nb078AlphaDummy1199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1244)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1200 h) from (by
          unfold
            nb078AlphaDummy1200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1245
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1187) ≠
        (nb078AlphaDummy1195) from (by
          unfold
            nb078AlphaDummy1195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1242)
                  0)))) (show (nb078AlphaDummy1190 h) ≠ (nb078AlphaDummy1196 h) from (by
          unfold
            nb078AlphaDummy1196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1243
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                                  unfold nb078AlphaDummy1183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1226) 0)))) (show
                                (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from (by
                                  unfold nb078AlphaDummy1184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                              ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                              ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                              ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
                              ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
                              ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                              ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                              ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
                              ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                                unfold nb078AlphaDummy1183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1226) 0))))
                            (show (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from
                              (by
                                unfold nb078AlphaDummy1184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy1179) ≠ (nb078AlphaDummy1183) from (by
                                  unfold nb078AlphaDummy1183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1226) 0)))) (show
                                (nb078AlphaDummy1181 h) ≠ (nb078AlphaDummy1184 h) from (by
                                  unfold nb078AlphaDummy1184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1227 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy1183), (nb078AlphaDummy1184 h)),
                              ((nb078AlphaDummy1179), (nb078AlphaDummy1181 h)),
                              ((nb078AlphaDummy1180), (nb078AlphaDummy1182 h)),
                              ((nb078AlphaDummy1205), (nb078AlphaDummy1206 h)),
                              ((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)),
                              ((nb078AlphaDummy1172), (nb078AlphaDummy1174 h)),
                              ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
                              ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)),
                              ((nb078AlphaDummy1175), (nb078AlphaDummy1176 h)),
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part180`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0162`. -/
@[expose]
noncomputable def nb078SplitAlpha0162 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy859))
          (Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy859)) (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCphi (Class.cv (nb078AlphaDummy854)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy860 h))
          (Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy860 h))
            (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCphi (Class.cv (nb078AlphaDummy856 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy854) from
                    (by
                      unfold nb078AlphaDummy854;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                  (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy856 h) from (by
                      unfold nb078AlphaDummy856;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy853) from
                      (by
                        unfold nb078AlphaDummy853;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                    (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy855 h) from (by
                        unfold nb078AlphaDummy855;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy859) from (by
                          unfold nb078AlphaDummy859;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy860 h) from (by
                          unfold nb078AlphaDummy860;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy857) from (by
                            unfold nb078AlphaDummy857;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy858 h) from (by
                            unfold nb078AlphaDummy858;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy847))).fv ∪
                      ((Class.cv (nb078AlphaDummy848))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy849 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy850 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                              unfold nb078AlphaDummy861;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                          (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                              unfold nb078AlphaDummy863;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from (by
                                unfold nb078AlphaDummy862;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                            (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                                unfold nb078AlphaDummy864;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
          unfold nb078AlphaDummy868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
          unfold nb078AlphaDummy871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from (by
          unfold nb078AlphaDummy867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
          unfold nb078AlphaDummy870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy863
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                        unfold nb078AlphaDummy865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy866 h) from (by
                                        unfold nb078AlphaDummy866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                    ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                    ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                    ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                    ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                    ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                    ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from
                                    (by
                                      unfold nb078AlphaDummy865;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0890)
                                              0)))) (show
                                    (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                    (by
                                      unfold nb078AlphaDummy866;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0891 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                        unfold nb078AlphaDummy865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy866 h) from (by
                                        unfold nb078AlphaDummy866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                    ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                    ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                    ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                    ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                    ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                    ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy854) from
                      (by
                        unfold nb078AlphaDummy854;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                    (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy856 h) from (by
                        unfold nb078AlphaDummy856;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy853) from (by
                          unfold nb078AlphaDummy853;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy855 h) from (by
                          unfold nb078AlphaDummy855;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy859) from (by
                            unfold nb078AlphaDummy859;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy860 h) from (by
                            unfold nb078AlphaDummy860;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy857) from (by
                              unfold nb078AlphaDummy857;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                          (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy858 h) from (by
                              unfold nb078AlphaDummy858;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv)
                              (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy847))).fv ∪
                        ((Class.cv (nb078AlphaDummy848))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy849 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy850 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                                unfold nb078AlphaDummy861;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                            (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                                unfold nb078AlphaDummy863;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from (by
                                  unfold nb078AlphaDummy862;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                              (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from
                                (by
                                  unfold nb078AlphaDummy864;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy856 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
          unfold nb078AlphaDummy868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
          unfold nb078AlphaDummy871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from (by
          unfold nb078AlphaDummy867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
          unfold nb078AlphaDummy870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865)
        from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890)
                  0)))) (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy863
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from
                                        (by
                                          unfold nb078AlphaDummy865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
                                          unfold nb078AlphaDummy866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                      ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                      ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                      ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                      ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                      ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                      ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                        unfold nb078AlphaDummy865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy866 h) from (by
                                        unfold nb078AlphaDummy866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from
                                        (by
                                          unfold nb078AlphaDummy865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
                                          unfold nb078AlphaDummy866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                      ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                      ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                      ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                      ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                      ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                      ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
