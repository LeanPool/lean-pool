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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0131`. -/
@[expose]
noncomputable def nb078SplitAlpha0131 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
        ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1041))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy1010))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1041)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1042 h))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy1012 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1042 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from (by
                              unfold nb078AlphaDummy1017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                          (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1019 h) from (by
                              unfold nb078AlphaDummy1019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from (by
                                unfold nb078AlphaDummy1018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 1))))
                            (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1020 h) from
                              (by
                                unfold nb078AlphaDummy1020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1043) from (by
                                  unfold nb078AlphaDummy1043;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1084) 0)))) (show
                                (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1044 h) from (by
                                  unfold nb078AlphaDummy1044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1085 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1041) from
                                  (by
                                    unfold nb078AlphaDummy1041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1082) 0)))) (show
                                  (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1042 h) from
                                  (by
                                    unfold nb078AlphaDummy1042;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1083 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1012 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
        ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
        ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                    ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                    ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                    ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
                                    ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
                                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                    ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
                                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                    ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                    ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
                                      unfold nb078AlphaDummy1021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1056)
                                              0)))) (show (nb078AlphaDummy1019 h) ≠
                                      (nb078AlphaDummy1022 h) from (by
                                      unfold nb078AlphaDummy1022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1057 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                    ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                    ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                    ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
                                    ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
                                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                    ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
                                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                    ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                    ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from (by
                              unfold nb078AlphaDummy1017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                          (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1019 h) from (by
                              unfold nb078AlphaDummy1019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from (by
                                unfold nb078AlphaDummy1018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 1))))
                            (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1020 h) from
                              (by
                                unfold nb078AlphaDummy1020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1043) from (by
                                  unfold nb078AlphaDummy1043;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1084) 0)))) (show
                                (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1044 h) from (by
                                  unfold nb078AlphaDummy1044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1085 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1041) from
                                  (by
                                    unfold nb078AlphaDummy1041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1082) 0)))) (show
                                  (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1042 h) from
                                  (by
                                    unfold nb078AlphaDummy1042;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1083 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1012 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
        ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
        ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                    ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                    ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                    ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
                                    ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
                                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                    ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
                                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                    ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                    ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
                                      unfold nb078AlphaDummy1021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1056)
                                              0)))) (show (nb078AlphaDummy1019 h) ≠
                                      (nb078AlphaDummy1022 h) from (by
                                      unfold nb078AlphaDummy1022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1057 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                    ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                    ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                    ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
                                    ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
                                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                    ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
                                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                    ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                    ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
            ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
            ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
            ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
            ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
            ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
            ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
            ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
            ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0132`. -/
@[expose]
noncomputable def nb078SplitAlpha0132 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1010))
          (Class.cv (nb078AlphaDummy1005))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy1009))
            (synCun (synCphi (Class.cv (nb078AlphaDummy1010))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1012 h))
          (Class.cv (nb078AlphaDummy1007 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
            (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1010) from (by
              unfold nb078AlphaDummy1010;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))))
          (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1012 h) from (by
              unfold nb078AlphaDummy1012;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1009) from (by
                unfold nb078AlphaDummy1009;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))))
            (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1011 h) from (by
                unfold nb078AlphaDummy1011;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1039) from (by
                  unfold nb078AlphaDummy1039;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1080) 0))))
              (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1040 h) from (by
                  unfold nb078AlphaDummy1040;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1081 h) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1013) from
                  (by
                    unfold nb078AlphaDummy1013;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1077) 0))))
                (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1014 h) from (by
                    unfold nb078AlphaDummy1014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1079 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv h)).fv ∪ ((synCvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078AlphaDummy1006))).fv ∪
                ((Class.cv (nb078AlphaDummy1005))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
                ((Class.cv (nb078AlphaDummy1007 h))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from
                                      (by
                                        unfold nb078AlphaDummy1017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                0)))) (show (nb078AlphaDummy1012 h) ≠
                                        (nb078AlphaDummy1019 h) from (by
                                        unfold nb078AlphaDummy1019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from
                                        (by
                                          unfold nb078AlphaDummy1018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1054)
                                                  1)))) (show (nb078AlphaDummy1012 h) ≠
        (nb078AlphaDummy1020 h) from (by
                                          unfold nb078AlphaDummy1020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1055 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1010) ≠
        (nb078AlphaDummy1043) from (by
          unfold nb078AlphaDummy1043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1084) 0)))) (show (nb078AlphaDummy1012 h) ≠
        (nb078AlphaDummy1044 h) from (by
          unfold nb078AlphaDummy1044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1085 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1041) from (by
          unfold nb078AlphaDummy1041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1082) 0)))) (show (nb078AlphaDummy1012 h) ≠
        (nb078AlphaDummy1042 h) from (by
          unfold nb078AlphaDummy1042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1083 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy1010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy1012 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold
            nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1022 h) from (by
          unfold
            nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
        ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018),
        (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
        ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
        ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018),
        (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
        ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from
                                      (by
                                        unfold nb078AlphaDummy1017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                0)))) (show (nb078AlphaDummy1012 h) ≠
                                        (nb078AlphaDummy1019 h) from (by
                                        unfold nb078AlphaDummy1019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from
                                        (by
                                          unfold nb078AlphaDummy1018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1054)
                                                  1)))) (show (nb078AlphaDummy1012 h) ≠
        (nb078AlphaDummy1020 h) from (by
                                          unfold nb078AlphaDummy1020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1055 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1010) ≠
        (nb078AlphaDummy1043) from (by
          unfold nb078AlphaDummy1043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1084) 0)))) (show (nb078AlphaDummy1012 h) ≠
        (nb078AlphaDummy1044 h) from (by
          unfold nb078AlphaDummy1044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1085 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1041) from (by
          unfold nb078AlphaDummy1041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1082) 0)))) (show (nb078AlphaDummy1012 h) ≠
        (nb078AlphaDummy1042 h) from (by
          unfold nb078AlphaDummy1042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1083 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy1010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy1012 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold
            nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1022 h) from (by
          unfold
            nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)), ((nb078AlphaDummy1041),
        (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
        ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1039),
        (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005),
        (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
        ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018),
        (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
        ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
        ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018),
        (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1043), (nb078AlphaDummy1044 h)),
        ((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy1041), (nb078AlphaDummy1042 h)),
                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                    ((nb078AlphaDummy1039), (nb078AlphaDummy1040 h)),
                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0133`. -/
@[expose]
noncomputable def nb078SplitAlpha0133 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1013)) (synCcompl
            (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCphi (Class.cv (nb078AlphaDummy1010)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1013)) (synCcompl
              (Class.cab (nb078AlphaDummy1009)
                (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
                  (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1014 h)) (synCcompl
            (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCphi (Class.cv (nb078AlphaDummy1012 h)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1014 h)) (synCcompl
              (Class.cab (nb078AlphaDummy1011 h)
                (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
                  (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1010) from (by
                              unfold nb078AlphaDummy1010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                          (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1012 h) from (by
                              unfold nb078AlphaDummy1012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1009) from (by
                                unfold nb078AlphaDummy1009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                            (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1011 h) from
                              (by
                                unfold nb078AlphaDummy1011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1015) from (by
                                  unfold nb078AlphaDummy1015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1052) 0)))) (show
                                (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1016 h) from (by
                                  unfold nb078AlphaDummy1016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1013) from
                                  (by
                                    unfold nb078AlphaDummy1013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1049) 0)))) (show
                                  (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1014 h) from
                                  (by
                                    unfold nb078AlphaDummy1014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1051 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy1006))).fv ∪
                              ((Class.cv (nb078AlphaDummy1005))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
                              ((Class.cv (nb078AlphaDummy1007 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from (by
                                      unfold nb078AlphaDummy1017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1054)
                                              0)))) (show (nb078AlphaDummy1012 h) ≠
                                      (nb078AlphaDummy1019 h) from (by
                                      unfold nb078AlphaDummy1019;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1055 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from
                                      (by
                                        unfold nb078AlphaDummy1018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                1)))) (show (nb078AlphaDummy1012 h) ≠
                                        (nb078AlphaDummy1020 h) from (by
                                        unfold nb078AlphaDummy1020;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy1012 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021),
        (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
        ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021),
        (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
        ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1010) from (by
                              unfold nb078AlphaDummy1010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                          (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1012 h) from (by
                              unfold nb078AlphaDummy1012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1009) from (by
                                unfold nb078AlphaDummy1009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                            (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1011 h) from
                              (by
                                unfold nb078AlphaDummy1011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1015) from (by
                                  unfold nb078AlphaDummy1015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1052) 0)))) (show
                                (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1016 h) from (by
                                  unfold nb078AlphaDummy1016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1013) from
                                  (by
                                    unfold nb078AlphaDummy1013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1049) 0)))) (show
                                  (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1014 h) from
                                  (by
                                    unfold nb078AlphaDummy1014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1051 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy1006))).fv ∪
                              ((Class.cv (nb078AlphaDummy1005))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
                              ((Class.cv (nb078AlphaDummy1007 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from (by
                                      unfold nb078AlphaDummy1017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1054)
                                              0)))) (show (nb078AlphaDummy1012 h) ≠
                                      (nb078AlphaDummy1019 h) from (by
                                      unfold nb078AlphaDummy1019;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1055 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from
                                      (by
                                        unfold nb078AlphaDummy1018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1054)
                                                1)))) (show (nb078AlphaDummy1012 h) ≠
                                        (nb078AlphaDummy1020 h) from (by
                                        unfold nb078AlphaDummy1020;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1055 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy1012 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  1)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021),
        (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
        ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy1021),
        (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
        ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)), ((nb078AlphaDummy1010),
        (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
        ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)), ((nb078AlphaDummy1013),
        (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0132 x y h)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0132 x y h)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
