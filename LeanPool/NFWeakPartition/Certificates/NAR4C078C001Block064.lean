/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block063

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part185`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0168`. -/
@[expose]
noncomputable def nb078SplitAlpha0168 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)),
        ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
        ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
        ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)),
        ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1239))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy1208))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1239)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1240 h))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy1210 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1240 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1215) from (by
                              unfold nb078AlphaDummy1215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                          (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1217 h) from (by
                              unfold nb078AlphaDummy1217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1216) from (by
                                unfold nb078AlphaDummy1216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 1))))
                            (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1218 h) from
                              (by
                                unfold nb078AlphaDummy1218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1241) from (by
                                  unfold nb078AlphaDummy1241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1304) 0)))) (show
                                (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1242 h) from (by
                                  unfold nb078AlphaDummy1242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1305 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1239) from
                                  (by
                                    unfold nb078AlphaDummy1239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1302) 0)))) (show
                                  (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1240 h) from
                                  (by
                                    unfold nb078AlphaDummy1240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1303 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1208))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1222) from (by
          unfold nb078AlphaDummy1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1225 h) from (by
          unfold nb078AlphaDummy1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1221) from (by
          unfold nb078AlphaDummy1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1224 h) from (by
          unfold nb078AlphaDummy1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from (by
          unfold nb078AlphaDummy1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1220 h) from (by
          unfold nb078AlphaDummy1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)), ((nb078AlphaDummy1239),
        (nb078AlphaDummy1240 h)), ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
        ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1237),
        (nb078AlphaDummy1238 h)), ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)), ((nb078AlphaDummy1239),
        (nb078AlphaDummy1240 h)), ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
        ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1237),
        (nb078AlphaDummy1238 h)), ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1217
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                    ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                    ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                    ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)),
                                    ((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)),
                                    ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                    ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                    ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)),
                                    ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from (by
                                      unfold nb078AlphaDummy1219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1276)
                                              0)))) (show (nb078AlphaDummy1217 h) ≠
                                      (nb078AlphaDummy1220 h) from (by
                                      unfold nb078AlphaDummy1220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1277 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                    ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                    ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                    ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)),
                                    ((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)),
                                    ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                    ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                    ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)),
                                    ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1215) from (by
                              unfold nb078AlphaDummy1215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                          (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1217 h) from (by
                              unfold nb078AlphaDummy1217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1216) from (by
                                unfold nb078AlphaDummy1216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 1))))
                            (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1218 h) from
                              (by
                                unfold nb078AlphaDummy1218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1241) from (by
                                  unfold nb078AlphaDummy1241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1304) 0)))) (show
                                (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1242 h) from (by
                                  unfold nb078AlphaDummy1242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1305 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1239) from
                                  (by
                                    unfold nb078AlphaDummy1239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1302) 0)))) (show
                                  (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1240 h) from
                                  (by
                                    unfold nb078AlphaDummy1240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1303 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1208))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1222) from (by
          unfold nb078AlphaDummy1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1225 h) from (by
          unfold nb078AlphaDummy1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1221) from (by
          unfold nb078AlphaDummy1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1224 h) from (by
          unfold nb078AlphaDummy1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from (by
          unfold nb078AlphaDummy1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1220 h) from (by
          unfold nb078AlphaDummy1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)), ((nb078AlphaDummy1239),
        (nb078AlphaDummy1240 h)), ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
        ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1237),
        (nb078AlphaDummy1238 h)), ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)), ((nb078AlphaDummy1239),
        (nb078AlphaDummy1240 h)), ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
        ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1237),
        (nb078AlphaDummy1238 h)), ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1217
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                    ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                    ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                    ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)),
                                    ((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)),
                                    ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                    ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                    ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)),
                                    ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from (by
                                      unfold nb078AlphaDummy1219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1276)
                                              0)))) (show (nb078AlphaDummy1217 h) ≠
                                      (nb078AlphaDummy1220 h) from (by
                                      unfold nb078AlphaDummy1220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1277 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                    ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                    ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                    ((nb078AlphaDummy1241), (nb078AlphaDummy1242 h)),
                                    ((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)),
                                    ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                    ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                    ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)),
                                    ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)),
            ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
            ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
            ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)),
            ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part186`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0169`. -/
@[expose]
noncomputable def nb078SplitAlpha0169 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
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

/-! Certificates from `NAR4C078C001Part187`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0170`. -/
@[expose]
noncomputable def nb078SplitAlpha0170 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy887))
          (synCphi (Class.cv (nb078AlphaDummy854)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy887))
            (synCphi (Class.cv (nb078AlphaDummy854))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy888 h))
          (synCphi (Class.cv (nb078AlphaDummy856 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy888 h))
            (synCphi (Class.cv (nb078AlphaDummy856 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from
                    (by
                      unfold nb078AlphaDummy861;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                  (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                      unfold nb078AlphaDummy863;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from
                      (by
                        unfold nb078AlphaDummy862;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                    (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                        unfold nb078AlphaDummy864;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy887) from (by
                          unfold nb078AlphaDummy887;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                      (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy888 h) from (by
                          unfold nb078AlphaDummy888;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy885) from (by
                            unfold nb078AlphaDummy885;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                        (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy886 h) from (by
                            unfold nb078AlphaDummy886;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
                                        unfold nb078AlphaDummy868;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0892)
                                                1)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy871 h) from (by
                                        unfold nb078AlphaDummy871;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0893 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from
                                        (by
                                          unfold nb078AlphaDummy867;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
                                          unfold nb078AlphaDummy870;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy861) ≠
        (nb078AlphaDummy865) from (by
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
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy869),
        (nb078AlphaDummy872 h)), ((nb078AlphaDummy868), (nb078AlphaDummy871 h)),
                                        ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
                                        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                        ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                        ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                        ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                                        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                                        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                                        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy875) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)),
        ((nb078AlphaDummy868), (nb078AlphaDummy871 h)), ((nb078AlphaDummy867),
        (nb078AlphaDummy870 h)), ((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
        ((nb078AlphaDummy861), (nb078AlphaDummy863 h)), ((nb078AlphaDummy862),
        (nb078AlphaDummy864 h)), ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy879) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                            ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                            ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                            ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                            ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                            ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                            ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                            ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                            ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                              unfold nb078AlphaDummy865;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                          (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                              unfold nb078AlphaDummy866;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                            ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                            ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                            ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                            ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                            ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                            ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                            ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                            ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
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
                    (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                        unfold nb078AlphaDummy861;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                    (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                        unfold nb078AlphaDummy863;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 0)))) (TAlphaVar.there
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
                      (TAlphaVar.there
                        (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy887) from (by
                            unfold nb078AlphaDummy887;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                        (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy888 h) from (by
                            unfold nb078AlphaDummy888;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy885) from (by
                              unfold nb078AlphaDummy885;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                          (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy886 h) from (by
                              unfold nb078AlphaDummy886;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from
                                        (by
                                          unfold nb078AlphaDummy868;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
                                          unfold nb078AlphaDummy871;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy861) ≠
        (nb078AlphaDummy867) from (by
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
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy869),
        (nb078AlphaDummy872 h)), ((nb078AlphaDummy868), (nb078AlphaDummy871 h)),
        ((nb078AlphaDummy867), (nb078AlphaDummy870 h)), ((nb078AlphaDummy865),
        (nb078AlphaDummy866 h)), ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
        ((nb078AlphaDummy862), (nb078AlphaDummy864 h)), ((nb078AlphaDummy887),
        (nb078AlphaDummy888 h)), ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy875) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy887), (nb078AlphaDummy888 h)), ((nb078AlphaDummy885),
        (nb078AlphaDummy886 h)), ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)), ((nb078AlphaDummy883),
        (nb078AlphaDummy884 h)), ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy879) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                  unfold nb078AlphaDummy865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                (by
                                  unfold nb078AlphaDummy866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                              ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                              ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                              ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                              ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                              ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                              ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                              ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                              ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                  unfold nb078AlphaDummy865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                (by
                                  unfold nb078AlphaDummy866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                              ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                              ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                              ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                              ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                              ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                              ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                              ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                              ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
