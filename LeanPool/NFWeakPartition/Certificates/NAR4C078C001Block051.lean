/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block050

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part152`. -/


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
noncomputable def nb078_split_alpha_0131 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
        ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1041))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1041)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1042 h))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1042 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from (by
                              unfold nb078_alpha_dummy_1017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                          (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1019 h) from (by
                              unfold nb078_alpha_dummy_1019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from (by
                                unfold nb078_alpha_dummy_1018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 1))))
                            (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1020 h) from
                              (by
                                unfold nb078_alpha_dummy_1020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1043) from (by
                                  unfold nb078_alpha_dummy_1043;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1084) 0)))) (show
                                (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1044 h) from (by
                                  unfold nb078_alpha_dummy_1044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1085 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1041) from
                                  (by
                                    unfold nb078_alpha_dummy_1041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1082) 0)))) (show
                                  (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1042 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1042;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1083 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
        ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
        ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                    ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                    ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                    ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
                                    ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
                                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                    ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
                                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
                                      unfold nb078_alpha_dummy_1021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1056)
                                              0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                      (nb078_alpha_dummy_1022 h) from (by
                                      unfold nb078_alpha_dummy_1022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1057 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                    ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                    ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                    ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
                                    ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
                                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                    ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
                                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from (by
                              unfold nb078_alpha_dummy_1017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                          (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1019 h) from (by
                              unfold nb078_alpha_dummy_1019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from (by
                                unfold nb078_alpha_dummy_1018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 1))))
                            (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1020 h) from
                              (by
                                unfold nb078_alpha_dummy_1020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1043) from (by
                                  unfold nb078_alpha_dummy_1043;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1084) 0)))) (show
                                (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1044 h) from (by
                                  unfold nb078_alpha_dummy_1044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1085 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1041) from
                                  (by
                                    unfold nb078_alpha_dummy_1041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1082) 0)))) (show
                                  (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1042 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1042;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1083 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
        ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
        ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                    ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                    ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                    ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
                                    ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
                                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                    ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
                                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
                                      unfold nb078_alpha_dummy_1021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1056)
                                              0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                      (nb078_alpha_dummy_1022 h) from (by
                                      unfold nb078_alpha_dummy_1022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1057 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                    ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                    ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                    ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
                                    ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
                                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                    ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
                                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
            ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
            ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
            ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
            ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
            ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
            ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
            ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
            ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part153`. -/


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
noncomputable def nb078_split_alpha_0132 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1010))
          (Class.cv (nb078_alpha_dummy_1005))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1012 h))
          (Class.cv (nb078_alpha_dummy_1007 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
              unfold nb078_alpha_dummy_1010;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))))
          (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
              unfold nb078_alpha_dummy_1012;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1009) from (by
                unfold nb078_alpha_dummy_1009;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))))
            (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
                unfold nb078_alpha_dummy_1011;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1039) from (by
                  unfold nb078_alpha_dummy_1039;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1080) 0))))
              (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1040 h) from (by
                  unfold nb078_alpha_dummy_1040;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1081 h) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1013) from
                  (by
                    unfold nb078_alpha_dummy_1013;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1077) 0))))
                (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1014 h) from (by
                    unfold nb078_alpha_dummy_1014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1079 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_1006))).fv ∪
                ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
                ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from
                                      (by
                                        unfold nb078_alpha_dummy_1017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                0)))) (show (nb078_alpha_dummy_1012 h) ≠
                                        (nb078_alpha_dummy_1019 h) from (by
                                        unfold nb078_alpha_dummy_1019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from
                                        (by
                                          unfold nb078_alpha_dummy_1018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1054)
                                                  1)))) (show (nb078_alpha_dummy_1012 h) ≠
        (nb078_alpha_dummy_1020 h) from (by
                                          unfold nb078_alpha_dummy_1020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1055 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1010) ≠
        (nb078_alpha_dummy_1043) from (by
          unfold nb078_alpha_dummy_1043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1084) 0)))) (show (nb078_alpha_dummy_1012 h) ≠
        (nb078_alpha_dummy_1044 h) from (by
          unfold nb078_alpha_dummy_1044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1085 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1041) from (by
          unfold nb078_alpha_dummy_1041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1082) 0)))) (show (nb078_alpha_dummy_1012 h) ≠
        (nb078_alpha_dummy_1042 h) from (by
          unfold nb078_alpha_dummy_1042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1083 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold
            nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1022 h) from (by
          unfold
            nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
        ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018),
        (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
        ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
        ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018),
        (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
        ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from
                                      (by
                                        unfold nb078_alpha_dummy_1017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                0)))) (show (nb078_alpha_dummy_1012 h) ≠
                                        (nb078_alpha_dummy_1019 h) from (by
                                        unfold nb078_alpha_dummy_1019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from
                                        (by
                                          unfold nb078_alpha_dummy_1018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1054)
                                                  1)))) (show (nb078_alpha_dummy_1012 h) ≠
        (nb078_alpha_dummy_1020 h) from (by
                                          unfold nb078_alpha_dummy_1020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1055 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1010) ≠
        (nb078_alpha_dummy_1043) from (by
          unfold nb078_alpha_dummy_1043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1084) 0)))) (show (nb078_alpha_dummy_1012 h) ≠
        (nb078_alpha_dummy_1044 h) from (by
          unfold nb078_alpha_dummy_1044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1085 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1041) from (by
          unfold nb078_alpha_dummy_1041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1082) 0)))) (show (nb078_alpha_dummy_1012 h) ≠
        (nb078_alpha_dummy_1042 h) from (by
          unfold nb078_alpha_dummy_1042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1083 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold
            nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1022 h) from (by
          unfold
            nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041),
        (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
        ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039),
        (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005),
        (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
        ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018),
        (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
        ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
        ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018),
        (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)),
        ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)),
                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                    ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)),
                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb078_split_alpha_0133 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1013)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1013)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_1009)
                (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1014 h)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1014 h)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_1011 h)
                (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1010) from (by
                              unfold nb078_alpha_dummy_1010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                          (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1012 h) from (by
                              unfold nb078_alpha_dummy_1012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1009) from (by
                                unfold nb078_alpha_dummy_1009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                            (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1011 h) from
                              (by
                                unfold nb078_alpha_dummy_1011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1015) from (by
                                  unfold nb078_alpha_dummy_1015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1052) 0)))) (show
                                (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1016 h) from (by
                                  unfold nb078_alpha_dummy_1016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1013) from
                                  (by
                                    unfold nb078_alpha_dummy_1013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1049) 0)))) (show
                                  (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1014 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1051 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_1006))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from (by
                                      unfold nb078_alpha_dummy_1017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1054)
                                              0)))) (show (nb078_alpha_dummy_1012 h) ≠
                                      (nb078_alpha_dummy_1019 h) from (by
                                      unfold nb078_alpha_dummy_1019;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1055 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from
                                      (by
                                        unfold nb078_alpha_dummy_1018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                1)))) (show (nb078_alpha_dummy_1012 h) ≠
                                        (nb078_alpha_dummy_1020 h) from (by
                                        unfold nb078_alpha_dummy_1020;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021),
        (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
        ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021),
        (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
        ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1010) from (by
                              unfold nb078_alpha_dummy_1010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                          (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1012 h) from (by
                              unfold nb078_alpha_dummy_1012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1009) from (by
                                unfold nb078_alpha_dummy_1009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                            (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1011 h) from
                              (by
                                unfold nb078_alpha_dummy_1011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1015) from (by
                                  unfold nb078_alpha_dummy_1015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1052) 0)))) (show
                                (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1016 h) from (by
                                  unfold nb078_alpha_dummy_1016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1013) from
                                  (by
                                    unfold nb078_alpha_dummy_1013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1049) 0)))) (show
                                  (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1014 h) from
                                  (by
                                    unfold nb078_alpha_dummy_1014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1051 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_1006))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from (by
                                      unfold nb078_alpha_dummy_1017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1054)
                                              0)))) (show (nb078_alpha_dummy_1012 h) ≠
                                      (nb078_alpha_dummy_1019 h) from (by
                                      unfold nb078_alpha_dummy_1019;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1055 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from
                                      (by
                                        unfold nb078_alpha_dummy_1018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                1)))) (show (nb078_alpha_dummy_1012 h) ≠
                                        (nb078_alpha_dummy_1020 h) from (by
                                        unfold nb078_alpha_dummy_1020;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021),
        (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
        ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1021),
        (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
        ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010),
        (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
        ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013),
        (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0132 x y h)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0132 x y h)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
