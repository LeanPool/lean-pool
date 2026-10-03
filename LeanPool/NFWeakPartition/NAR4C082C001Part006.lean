/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C082C001Part006Stage1


/-! NF weak partition development: NAR4C082C001Part006. -/


public section


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
noncomputable def nb082_wpp_refl_0008 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    TReflOn
      [((nb082_alpha_dummy_050 A B R), (nb082_alpha_dummy_052 A B R p)),
        ((nb082_alpha_dummy_049 A B R), (nb082_alpha_dummy_051 A B R p)),
        ((nb082_alpha_dummy_047 A B R), (nb082_alpha_dummy_048 A B R p)),
        ((nb082_alpha_dummy_045 A B R), (nb082_alpha_dummy_046 A B R p)),
        ((nb082_alpha_dummy_042 A B R), (nb082_alpha_dummy_044 A B R p)),
        ((nb082_alpha_dummy_041 A B R), (nb082_alpha_dummy_043 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      ((syn_ccnvk (syn_cfdminsep R A B))).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0008 A B R p dv_A_p dv_B_p dv_R_p)

@[expose]
noncomputable def nb082_split_alpha_0003 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    TAlphaWff
      [((nb082_alpha_dummy_045 A B R), (nb082_alpha_dummy_046 A B R p)),
        ((nb082_alpha_dummy_042 A B R), (nb082_alpha_dummy_044 A B R p)),
        ((nb082_alpha_dummy_041 A B R), (nb082_alpha_dummy_043 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb082_alpha_dummy_045 A B R)) (syn_cnin
            (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb082_alpha_dummy_045 A B R)) (syn_cnin
              (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c)))))
      (Wff.imp (Wff.classMem (Class.cv (nb082_alpha_dummy_046 A B R p))
          (syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))) (Wff.neg (Wff.classMem (Class.cv (nb082_alpha_dummy_046 A B R p))
            (syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                  (nb082_alpha_dummy_053 A B R) from (by
                                  unfold nb082_alpha_dummy_053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb082_support_mem_0052 A B R)
                                          0)))) (show p ≠ (nb082_alpha_dummy_054 p) from (by
                                  unfold nb082_alpha_dummy_054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb082_support_mem_0053 p) 0))))
                              (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                    (nb082_alpha_dummy_050 A B R) from (by
                                    unfold nb082_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0050 A B R)
                                            1)))) (show p ≠ (nb082_alpha_dummy_052 A B R p) from
                                  (by
                                    unfold nb082_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb082_support_mem_0051 A B R p) 1))))
                                (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                      (nb082_alpha_dummy_049 A B R) from (by
                                      unfold nb082_alpha_dummy_049;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0050 A B R) 0))))
                                  (show p ≠ (nb082_alpha_dummy_051 A B R p) from (by
                                      unfold nb082_alpha_dummy_051;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0051 A B R p) 0))))
                                  (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                        (nb082_alpha_dummy_047 A B R) from (by
                                        unfold nb082_alpha_dummy_047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0048 A B R) 0))))
                                    (show p ≠ (nb082_alpha_dummy_048 A B R p) from (by
                                        unfold nb082_alpha_dummy_048;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0049 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_045 A B R) from (by
                                          unfold nb082_alpha_dummy_045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0046 A B R) 0))))
                                      (show p ≠ (nb082_alpha_dummy_046 A B R p) from (by
                                          unfold nb082_alpha_dummy_046;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0047 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_042 A B R) from (by
          unfold nb082_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R) 1))))
                                        (show p ≠ (nb082_alpha_dummy_044 A B R p) from (by
          unfold nb082_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p) 1)))) (TAlphaVar.there (show
        (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_041 A B R) from (by
          unfold nb082_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R) 0))))
        (show p ≠ (nb082_alpha_dummy_043 A B R p) from (by
          unfold nb082_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_001 A B R) from (by
          unfold nb082_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R)
                  0)))) (show p ≠ (nb082_alpha_dummy_002 A B R p) from (by
          unfold nb082_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0005 A B R p)
                  0)))) (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_050 A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_059 A B R) from (by
          unfold nb082_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_060 A B R p)
        from (by
          unfold nb082_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_057 A B R) from (by
          unfold nb082_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_058 A B R p)
        from (by
          unfold nb082_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_050 A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_059 A B R) from (by
          unfold nb082_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_060 A B R p)
        from (by
          unfold nb082_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_057 A B R) from (by
          unfold nb082_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_058 A B R p)
        from (by
          unfold nb082_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_050
        A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_050
        A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠ (nb082_alpha_dummy_073 A B R)
        from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_049
        A B R) ≠ (nb082_alpha_dummy_073 A B R) from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_050
        A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_050
        A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠ (nb082_alpha_dummy_073 A B R)
        from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_049
        A B R) ≠ (nb082_alpha_dummy_073 A B R) from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))
                      (TAlphaClass.refl_of_reflOn
                        [((nb082_alpha_dummy_050 A B R), (nb082_alpha_dummy_052 A B R p)),
                          ((nb082_alpha_dummy_049 A B R), (nb082_alpha_dummy_051 A B R p)),
                          ((nb082_alpha_dummy_047 A B R), (nb082_alpha_dummy_048 A B R p)),
                          ((nb082_alpha_dummy_045 A B R), (nb082_alpha_dummy_046 A B R p)),
                          ((nb082_alpha_dummy_042 A B R), (nb082_alpha_dummy_044 A B R p)),
                          ((nb082_alpha_dummy_041 A B R), (nb082_alpha_dummy_043 A B R p)),
                          ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
                          ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
                            (nb082_alpha_dummy_004 A B R p))] (syn_ccnvk (syn_cfdminsep R A B))
                        (nb082_wpp_refl_0008 A B R p dv_A_p dv_B_p dv_R_p)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_closed
                [((nb082_alpha_dummy_047 A B R), (nb082_alpha_dummy_048 A B R p)),
                  ((nb082_alpha_dummy_045 A B R), (nb082_alpha_dummy_046 A B R p)),
                  ((nb082_alpha_dummy_042 A B R), (nb082_alpha_dummy_044 A B R p)),
                  ((nb082_alpha_dummy_041 A B R), (nb082_alpha_dummy_043 A B R p)),
                  ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
                  ((nb082_alpha_dummy_000 A B R), p),
                  ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
                (syn_c1c) (by simp only [fv_syn_c1c]))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_053 A B R)
                                  from (by
                                    unfold nb082_alpha_dummy_053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0052 A B R)
                                            0)))) (show p ≠ (nb082_alpha_dummy_054 p) from (by
                                    unfold nb082_alpha_dummy_054;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0053 p)
                                            0)))) (TAlphaVar.there (show
                                    (nb082_alpha_dummy_000 A B R) ≠
                                      (nb082_alpha_dummy_050 A B R) from (by
                                      unfold nb082_alpha_dummy_050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0050 A B R) 1))))
                                  (show p ≠ (nb082_alpha_dummy_052 A B R p) from (by
                                      unfold nb082_alpha_dummy_052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0051 A B R p) 1))))
                                  (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                        (nb082_alpha_dummy_049 A B R) from (by
                                        unfold nb082_alpha_dummy_049;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0050 A B R) 0))))
                                    (show p ≠ (nb082_alpha_dummy_051 A B R p) from (by
                                        unfold nb082_alpha_dummy_051;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0051 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_047 A B R) from (by
                                          unfold nb082_alpha_dummy_047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0048 A B R) 0))))
                                      (show p ≠ (nb082_alpha_dummy_048 A B R p) from (by
                                          unfold nb082_alpha_dummy_048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0049 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_045 A B R) from (by
          unfold nb082_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0046 A B R) 0))))
                                        (show p ≠ (nb082_alpha_dummy_046 A B R p) from (by
          unfold nb082_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0047 A B R p) 0)))) (TAlphaVar.there (show
        (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_042 A B R) from (by
          unfold nb082_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R) 1))))
        (show p ≠ (nb082_alpha_dummy_044 A B R p) from (by
          unfold nb082_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_041 A B R) from (by
          unfold nb082_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R)
                  0)))) (show p ≠ (nb082_alpha_dummy_043 A B R p) from (by
          unfold nb082_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_001 A B R) from (by
          unfold nb082_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R)
                  0)))) (show p ≠ (nb082_alpha_dummy_002 A B R p) from (by
          unfold nb082_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0005 A B R p)
                  0)))) (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠ (nb082_alpha_dummy_061 A B R)
        from (by
          unfold nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_059 A B R) from (by
          unfold nb082_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_060 A B R p)
        from (by
          unfold nb082_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_057 A B R) from (by
          unfold nb082_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_058 A B R p)
        from (by
          unfold nb082_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠ (nb082_alpha_dummy_061 A B R)
        from (by
          unfold nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_059 A B R) from (by
          unfold nb082_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_060 A B R p)
        from (by
          unfold nb082_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_057 A B R) from (by
          unfold nb082_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_058 A B R p)
        from (by
          unfold nb082_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠ (nb082_alpha_dummy_061 A B R)
        from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_050
        A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠ (nb082_alpha_dummy_073 A B R)
        from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_049
        A B R) ≠ (nb082_alpha_dummy_073 A B R) from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠ (nb082_alpha_dummy_061 A B R)
        from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_050
        A B R) ≠ (nb082_alpha_dummy_061 A B R) from (by
          unfold
            nb082_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_062 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_069 A B R) from (by
          unfold
            nb082_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_070 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_050 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_052 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0055
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠ (nb082_alpha_dummy_073 A B R)
        from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_049
        A B R) ≠ (nb082_alpha_dummy_073 A B R) from (by
          unfold
            nb082_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_074 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_071 A B R) from (by
          unfold
            nb082_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_072 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_067 A B R) from (by
          unfold
            nb082_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_068 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_065 A B R) from (by
          unfold
            nb082_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_066 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_063 A B R) from (by
          unfold
            nb082_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_064 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_049 A B R) ≠
        (nb082_alpha_dummy_055 A B R) from (by
          unfold
            nb082_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_051 A B R p) ≠ (nb082_alpha_dummy_056 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A
        B))).fv ∪ ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv) (by
          decide)) (freshVar_injective (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))
                        (TAlphaClass.refl_of_reflOn [((nb082_alpha_dummy_050 A B R),
                              (nb082_alpha_dummy_052 A B R p)), ((nb082_alpha_dummy_049 A B R),
                              (nb082_alpha_dummy_051 A B R p)), ((nb082_alpha_dummy_047 A B R),
                              (nb082_alpha_dummy_048 A B R p)), ((nb082_alpha_dummy_045 A B R),
                              (nb082_alpha_dummy_046 A B R p)), ((nb082_alpha_dummy_042 A B R),
                              (nb082_alpha_dummy_044 A B R p)), ((nb082_alpha_dummy_041 A B R),
                              (nb082_alpha_dummy_043 A B R p)), ((nb082_alpha_dummy_001 A B R),
                              (nb082_alpha_dummy_002 A B R p)),
                            ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
                              (nb082_alpha_dummy_004 A B R p))]
                          (syn_ccnvk (syn_cfdminsep R A B))
                          (nb082_wpp_refl_0008 A B R p dv_A_p dv_B_p dv_R_p)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb082_alpha_dummy_047 A B R), (nb082_alpha_dummy_048 A B R p)),
                    ((nb082_alpha_dummy_045 A B R), (nb082_alpha_dummy_046 A B R p)),
                    ((nb082_alpha_dummy_042 A B R), (nb082_alpha_dummy_044 A B R p)),
                    ((nb082_alpha_dummy_041 A B R), (nb082_alpha_dummy_043 A B R p)),
                    ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
                    ((nb082_alpha_dummy_000 A B R), p),
                    ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
                  (syn_c1c) (by simp only [fv_syn_c1c])))))))))

@[expose]
noncomputable def nominal_df_fdpivmap2 (A : Class) (B : Class) (R : Class) (p : Var)
    (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_cfdpivmap2 R A B)
        (syn_cmpt p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb082_split_alpha_0002 A B R p) (TAlphaWff.conj (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_001 A B R) from
                        (by
                          unfold nb082_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0004 A B R) 0))))
                      (show p ≠ (nb082_alpha_dummy_002 A B R p) from (by
                          unfold nb082_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0005 A B R p) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
                    [((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
                      ((nb082_alpha_dummy_000 A B R), p),
                      ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
                    (syn_cxpk B B) (nb082_wpp_refl_0007 A B R p dv_B_p)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                            (freshVar_injective (((syn_cin
                                  (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                                    (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
                                  (syn_c1c))).fv) (by decide)) (freshVar_injective (((syn_cin
                                  (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                                    (syn_csn (Class.cv p))) (syn_c1c))).fv) (by decide))
                            (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb082_split_alpha_0003 A B R p dv_A_p dv_B_p
                                  dv_R_p))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
