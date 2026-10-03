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

@[expose]
noncomputable def nb078_split_alpha_0168 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)),
        ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
        ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
        ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)),
        ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1239))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1239)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1240 h))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1240 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1215) from (by
                              unfold nb078_alpha_dummy_1215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                          (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1217 h) from (by
                              unfold nb078_alpha_dummy_1217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1216) from (by
                                unfold nb078_alpha_dummy_1216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 1))))
                            (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1218 h) from
                              (by
                                unfold nb078_alpha_dummy_1218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1241) from (by
                                  unfold nb078_alpha_dummy_1241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1304) 0)))) (show
                                (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1242 h) from (by
                                  unfold nb078_alpha_dummy_1242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1305 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1239) from
                                  (by
                                    unfold nb078_alpha_dummy_1239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1302) 0)))) (show
                                  (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1240 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1303 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1222) from (by
          unfold nb078_alpha_dummy_1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1225 h) from (by
          unfold nb078_alpha_dummy_1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1221) from (by
          unfold nb078_alpha_dummy_1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1224 h) from (by
          unfold nb078_alpha_dummy_1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from (by
          unfold nb078_alpha_dummy_1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1220 h) from (by
          unfold nb078_alpha_dummy_1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)), ((nb078_alpha_dummy_1239),
        (nb078_alpha_dummy_1240 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
        ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1237),
        (nb078_alpha_dummy_1238 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)), ((nb078_alpha_dummy_1239),
        (nb078_alpha_dummy_1240 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
        ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1237),
        (nb078_alpha_dummy_1238 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                    ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                    ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                    ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)),
                                    ((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)),
                                    ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                    ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                    ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)),
                                    ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from (by
                                      unfold nb078_alpha_dummy_1219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1276)
                                              0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                      (nb078_alpha_dummy_1220 h) from (by
                                      unfold nb078_alpha_dummy_1220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1277 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                    ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                    ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                    ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)),
                                    ((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)),
                                    ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                    ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                    ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)),
                                    ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1215) from (by
                              unfold nb078_alpha_dummy_1215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                          (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1217 h) from (by
                              unfold nb078_alpha_dummy_1217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1216) from (by
                                unfold nb078_alpha_dummy_1216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 1))))
                            (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1218 h) from
                              (by
                                unfold nb078_alpha_dummy_1218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1241) from (by
                                  unfold nb078_alpha_dummy_1241;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1304) 0)))) (show
                                (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1242 h) from (by
                                  unfold nb078_alpha_dummy_1242;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1305 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1239) from
                                  (by
                                    unfold nb078_alpha_dummy_1239;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1302) 0)))) (show
                                  (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1240 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1240;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1303 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1222) from (by
          unfold nb078_alpha_dummy_1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1225 h) from (by
          unfold nb078_alpha_dummy_1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1221) from (by
          unfold nb078_alpha_dummy_1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1224 h) from (by
          unfold nb078_alpha_dummy_1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from (by
          unfold nb078_alpha_dummy_1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1220 h) from (by
          unfold nb078_alpha_dummy_1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)), ((nb078_alpha_dummy_1239),
        (nb078_alpha_dummy_1240 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
        ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1237),
        (nb078_alpha_dummy_1238 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)), ((nb078_alpha_dummy_1239),
        (nb078_alpha_dummy_1240 h)), ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
        ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1237),
        (nb078_alpha_dummy_1238 h)), ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                    ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                    ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                    ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)),
                                    ((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)),
                                    ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                    ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                    ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)),
                                    ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from (by
                                      unfold nb078_alpha_dummy_1219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1276)
                                              0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                      (nb078_alpha_dummy_1220 h) from (by
                                      unfold nb078_alpha_dummy_1220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1277 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                    ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                    ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                    ((nb078_alpha_dummy_1241), (nb078_alpha_dummy_1242 h)),
                                    ((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)),
                                    ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                    ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                    ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)),
                                    ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1239), (nb078_alpha_dummy_1240 h)),
            ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
            ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
            ((nb078_alpha_dummy_1237), (nb078_alpha_dummy_1238 h)),
            ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
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

@[expose]
noncomputable def nb078_split_alpha_0169 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879) from (by
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
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879) from (by
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
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
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

@[expose]
noncomputable def nb078_split_alpha_0170 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
        ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
        ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_887))
          (syn_cphi (Class.cv (nb078_alpha_dummy_854)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_887))
            (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_888 h))
          (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_888 h))
            (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from
                    (by
                      unfold nb078_alpha_dummy_861;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                  (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                      unfold nb078_alpha_dummy_863;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from
                      (by
                        unfold nb078_alpha_dummy_862;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                    (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from (by
                        unfold nb078_alpha_dummy_864;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_887) from (by
                          unfold nb078_alpha_dummy_887;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                      (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_888 h) from (by
                          unfold nb078_alpha_dummy_888;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_885) from (by
                            unfold nb078_alpha_dummy_885;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                        (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_886 h) from (by
                            unfold nb078_alpha_dummy_886;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from (by
                                        unfold nb078_alpha_dummy_868;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0892)
                                                1)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_871 h) from (by
                                        unfold nb078_alpha_dummy_871;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0893 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_867) from
                                        (by
                                          unfold nb078_alpha_dummy_867;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
                                          unfold nb078_alpha_dummy_870;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠
        (nb078_alpha_dummy_865) from (by
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
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_869),
        (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)),
                                        ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
                                        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                        ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                        ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                        ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                                        ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                                        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                        ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                                        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                        ((nb078_alpha_dummy_002), h),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_875) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)),
        ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867),
        (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
        ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862),
        (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
        ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                unfold nb078_alpha_dummy_865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                                unfold nb078_alpha_dummy_866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                            ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                            ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                            ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                            ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                            ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                            ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                            ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                            ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                              unfold nb078_alpha_dummy_865;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                          (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                              unfold nb078_alpha_dummy_866;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                unfold nb078_alpha_dummy_865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                                unfold nb078_alpha_dummy_866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                            ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                            ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                            ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                            ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                            ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                            ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                            ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                            ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from (by
                        unfold nb078_alpha_dummy_861;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                    (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                        unfold nb078_alpha_dummy_863;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 0)))) (TAlphaVar.there
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
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_887) from (by
                            unfold nb078_alpha_dummy_887;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                        (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_888 h) from (by
                            unfold nb078_alpha_dummy_888;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_885) from (by
                              unfold nb078_alpha_dummy_885;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                          (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_886 h) from (by
                              unfold nb078_alpha_dummy_886;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from
                                        (by
                                          unfold nb078_alpha_dummy_868;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  1)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_871 h) from (by
                                          unfold nb078_alpha_dummy_871;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠
        (nb078_alpha_dummy_867) from (by
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
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_869),
        (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)),
        ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865),
        (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
        ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887),
        (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_875) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885),
        (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
        ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883),
        (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                  unfold nb078_alpha_dummy_865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from
                                (by
                                  unfold nb078_alpha_dummy_866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                              ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                              ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                              ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                              ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                              ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                              ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                              ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                              ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                              ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                              ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                              ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                unfold nb078_alpha_dummy_865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                                unfold nb078_alpha_dummy_866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                  unfold nb078_alpha_dummy_865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from
                                (by
                                  unfold nb078_alpha_dummy_866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                              ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                              ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                              ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                              ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                              ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                              ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                              ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                              ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                              ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                              ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                              ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
