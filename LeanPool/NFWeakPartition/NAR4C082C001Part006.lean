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

/-- Checked nominal proof certificate identified upstream as `nb082_wpp_refl_0008`. -/
@[expose]
noncomputable def nb082WppRefl0008 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    TReflOn
      [((nb082AlphaDummy050 A B R), (nb082AlphaDummy052 A B R p)),
        ((nb082AlphaDummy049 A B R), (nb082AlphaDummy051 A B R p)),
        ((nb082AlphaDummy047 A B R), (nb082AlphaDummy048 A B R p)),
        ((nb082AlphaDummy045 A B R), (nb082AlphaDummy046 A B R p)),
        ((nb082AlphaDummy042 A B R), (nb082AlphaDummy044 A B R p)),
        ((nb082AlphaDummy041 A B R), (nb082AlphaDummy043 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      ((synCcnvk (synCfdminsep R A B))).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0008 A B R p dv_A_p dv_B_p dv_R_p)

/-- Checked nominal proof certificate identified upstream as `nb082_split_alpha_0003`. -/
@[expose]
noncomputable def nb082SplitAlpha0003 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    TAlphaWff
      [((nb082AlphaDummy045 A B R), (nb082AlphaDummy046 A B R p)),
        ((nb082AlphaDummy042 A B R), (nb082AlphaDummy044 A B R p)),
        ((nb082AlphaDummy041 A B R), (nb082AlphaDummy043 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb082AlphaDummy045 A B R)) (synCnin
            (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb082AlphaDummy045 A B R)) (synCnin
              (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv (nb082AlphaDummy046 A B R p))
          (synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))) (Wff.neg (Wff.classMem (Class.cv (nb082AlphaDummy046 A B R p))
            (synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                  (nb082AlphaDummy053 A B R) from (by
                                  unfold nb082AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb082_support_mem_0052 A B R)
                                          0)))) (show p ≠ (nb082AlphaDummy054 p) from (by
                                  unfold nb082AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb082_support_mem_0053 p) 0))))
                              (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                    (nb082AlphaDummy050 A B R) from (by
                                    unfold nb082AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0050 A B R)
                                            1)))) (show p ≠ (nb082AlphaDummy052 A B R p) from
                                  (by
                                    unfold nb082AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb082_support_mem_0051 A B R p) 1))))
                                (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                      (nb082AlphaDummy049 A B R) from (by
                                      unfold nb082AlphaDummy049;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0050 A B R) 0))))
                                  (show p ≠ (nb082AlphaDummy051 A B R p) from (by
                                      unfold nb082AlphaDummy051;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0051 A B R p) 0))))
                                  (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                        (nb082AlphaDummy047 A B R) from (by
                                        unfold nb082AlphaDummy047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0048 A B R) 0))))
                                    (show p ≠ (nb082AlphaDummy048 A B R p) from (by
                                        unfold nb082AlphaDummy048;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0049 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy045 A B R) from (by
                                          unfold nb082AlphaDummy045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0046 A B R) 0))))
                                      (show p ≠ (nb082AlphaDummy046 A B R p) from (by
                                          unfold nb082AlphaDummy046;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0047 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy042 A B R) from (by
          unfold nb082AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R) 1))))
                                        (show p ≠ (nb082AlphaDummy044 A B R p) from (by
          unfold nb082AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p) 1)))) (TAlphaVar.there (show
        (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy041 A B R) from (by
          unfold nb082AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R) 0))))
        (show p ≠ (nb082AlphaDummy043 A B R p) from (by
          unfold nb082AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy001 A B R) from (by
          unfold nb082AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R)
                  0)))) (show p ≠ (nb082AlphaDummy002 A B R p) from (by
          unfold nb082AlphaDummy002;
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
        (nb082AlphaDummy050 A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy059 A B R) from (by
          unfold nb082AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058 A
                    B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy060 A B R p)
        from (by
          unfold nb082AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy057 A B R) from (by
          unfold nb082AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy058 A B R p)
        from (by
          unfold nb082AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold nb082AlphaDummy056;
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
        (nb082AlphaDummy050 A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy059 A B R) from (by
          unfold nb082AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058 A
                    B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy060 A B R p)
        from (by
          unfold nb082AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy057 A B R) from (by
          unfold nb082AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy058 A B R p)
        from (by
          unfold nb082AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold nb082AlphaDummy056;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy050
        A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy050
        A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠ (nb082AlphaDummy073 A B R)
        from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy049
        A B R) ≠ (nb082AlphaDummy073 A B R) from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy050
        A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy050
        A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠ (nb082AlphaDummy073 A B R)
        from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy049
        A B R) ≠ (nb082AlphaDummy073 A B R) from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))
                      (TAlphaClass.reflOfReflOn
                        [((nb082AlphaDummy050 A B R), (nb082AlphaDummy052 A B R p)),
                          ((nb082AlphaDummy049 A B R), (nb082AlphaDummy051 A B R p)),
                          ((nb082AlphaDummy047 A B R), (nb082AlphaDummy048 A B R p)),
                          ((nb082AlphaDummy045 A B R), (nb082AlphaDummy046 A B R p)),
                          ((nb082AlphaDummy042 A B R), (nb082AlphaDummy044 A B R p)),
                          ((nb082AlphaDummy041 A B R), (nb082AlphaDummy043 A B R p)),
                          ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
                          ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
                            (nb082AlphaDummy004 A B R p))] (synCcnvk (synCfdminsep R A B))
                        (nb082WppRefl0008 A B R p dv_A_p dv_B_p dv_R_p)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfClosed
                [((nb082AlphaDummy047 A B R), (nb082AlphaDummy048 A B R p)),
                  ((nb082AlphaDummy045 A B R), (nb082AlphaDummy046 A B R p)),
                  ((nb082AlphaDummy042 A B R), (nb082AlphaDummy044 A B R p)),
                  ((nb082AlphaDummy041 A B R), (nb082AlphaDummy043 A B R p)),
                  ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
                  ((nb082AlphaDummy000 A B R), p),
                  ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
                (synC1c) (by simp only [fv_syn_c1c]))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy053 A B R)
                                  from (by
                                    unfold nb082AlphaDummy053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0052 A B R)
                                            0)))) (show p ≠ (nb082AlphaDummy054 p) from (by
                                    unfold nb082AlphaDummy054;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0053 p)
                                            0)))) (TAlphaVar.there (show
                                    (nb082AlphaDummy000 A B R) ≠
                                      (nb082AlphaDummy050 A B R) from (by
                                      unfold nb082AlphaDummy050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0050 A B R) 1))))
                                  (show p ≠ (nb082AlphaDummy052 A B R p) from (by
                                      unfold nb082AlphaDummy052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0051 A B R p) 1))))
                                  (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                        (nb082AlphaDummy049 A B R) from (by
                                        unfold nb082AlphaDummy049;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0050 A B R) 0))))
                                    (show p ≠ (nb082AlphaDummy051 A B R p) from (by
                                        unfold nb082AlphaDummy051;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0051 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy047 A B R) from (by
                                          unfold nb082AlphaDummy047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0048 A B R) 0))))
                                      (show p ≠ (nb082AlphaDummy048 A B R p) from (by
                                          unfold nb082AlphaDummy048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0049 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy045 A B R) from (by
          unfold nb082AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0046 A B R) 0))))
                                        (show p ≠ (nb082AlphaDummy046 A B R p) from (by
          unfold nb082AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0047 A B R p) 0)))) (TAlphaVar.there (show
        (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy042 A B R) from (by
          unfold nb082AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R) 1))))
        (show p ≠ (nb082AlphaDummy044 A B R p) from (by
          unfold nb082AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy041 A B R) from (by
          unfold nb082AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0044 A B R)
                  0)))) (show p ≠ (nb082AlphaDummy043 A B R p) from (by
          unfold nb082AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0045 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy001 A B R) from (by
          unfold nb082AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R)
                  0)))) (show p ≠ (nb082AlphaDummy002 A B R p) from (by
          unfold nb082AlphaDummy002;
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
        (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠ (nb082AlphaDummy061 A B R)
        from (by
          unfold nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A
                    B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy059 A B R) from (by
          unfold nb082AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy060 A B R p)
        from (by
          unfold nb082AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy057 A B R) from (by
          unfold nb082AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy058 A B R p)
        from (by
          unfold nb082AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠ (nb082AlphaDummy061 A B R)
        from (by
          unfold nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060 A
                    B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061 A
                    B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy059 A B R) from (by
          unfold nb082AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0058
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy060 A B R p)
        from (by
          unfold nb082AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0059
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy057 A B R) from (by
          unfold nb082AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0056
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy058 A B R p)
        from (by
          unfold nb082AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0057
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠ (nb082AlphaDummy061 A B R)
        from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy050
        A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠ (nb082AlphaDummy073 A B R)
        from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy049
        A B R) ≠ (nb082AlphaDummy073 A B R) from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠ (nb082AlphaDummy061 A B R)
        from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy050
        A B R) ≠ (nb082AlphaDummy061 A B R) from (by
          unfold
            nb082AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0060
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy062 A B R p)
        from (by
          unfold
            nb082AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0061
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy069 A B R) from (by
          unfold
            nb082AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0068
                    A B R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy070 A B R p)
        from (by
          unfold
            nb082AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0069
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0066
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0067
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0065
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0063
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy050 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0054
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy052 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
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
        (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠ (nb082AlphaDummy073 A B R)
        from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy049
        A B R) ≠ (nb082AlphaDummy073 A B R) from (by
          unfold
            nb082AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0080
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy074 A B R p)
        from (by
          unfold
            nb082AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0081
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy071 A B R) from (by
          unfold
            nb082AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0078
                    A B R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy072 A B R p)
        from (by
          unfold
            nb082AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0079
                    A B R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy067 A B R) from (by
          unfold
            nb082AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0076
                    A B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy068 A B R p)
        from (by
          unfold
            nb082AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0077
                    A B
                    R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy065 A B R) from (by
          unfold
            nb082AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0074
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy066 A B R p)
        from (by
          unfold
            nb082AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0075
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy063 A B R) from (by
          unfold
            nb082AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy064 A B R p)
        from (by
          unfold
            nb082AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0073
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy049 A B R) ≠
        (nb082AlphaDummy055 A B R) from (by
          unfold
            nb082AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy051 A B R p) ≠ (nb082AlphaDummy056 A B R p)
        from (by
          unfold
            nb082AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0071
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnvk (synCfdminsep R A
        B))).fv ∪ ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv) (by
          decide)) (freshVar_injective (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn
        (Class.cv p))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))
                        (TAlphaClass.reflOfReflOn [((nb082AlphaDummy050 A B R),
                              (nb082AlphaDummy052 A B R p)), ((nb082AlphaDummy049 A B R),
                              (nb082AlphaDummy051 A B R p)), ((nb082AlphaDummy047 A B R),
                              (nb082AlphaDummy048 A B R p)), ((nb082AlphaDummy045 A B R),
                              (nb082AlphaDummy046 A B R p)), ((nb082AlphaDummy042 A B R),
                              (nb082AlphaDummy044 A B R p)), ((nb082AlphaDummy041 A B R),
                              (nb082AlphaDummy043 A B R p)), ((nb082AlphaDummy001 A B R),
                              (nb082AlphaDummy002 A B R p)),
                            ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
                              (nb082AlphaDummy004 A B R p))]
                          (synCcnvk (synCfdminsep R A B))
                          (nb082WppRefl0008 A B R p dv_A_p dv_B_p dv_R_p)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb082AlphaDummy047 A B R), (nb082AlphaDummy048 A B R p)),
                    ((nb082AlphaDummy045 A B R), (nb082AlphaDummy046 A B R p)),
                    ((nb082AlphaDummy042 A B R), (nb082AlphaDummy044 A B R p)),
                    ((nb082AlphaDummy041 A B R), (nb082AlphaDummy043 A B R p)),
                    ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
                    ((nb082AlphaDummy000 A B R), p),
                    ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
                  (synC1c) (by simp only [fv_syn_c1c])))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_fdpivmap2`. -/
@[expose]
noncomputable def nominalDfFdpivmap2 (A : Class) (B : Class) (R : Class) (p : Var)
    (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synCfdpivmap2 R A B)
        (synCmpt p (synCxpk B B) (synCfdminvalp R A B (.cv p)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb082SplitAlpha0002 A B R p) (TAlphaWff.conj (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy001 A B R) from
                        (by
                          unfold nb082AlphaDummy001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0004 A B R) 0))))
                      (show p ≠ (nb082AlphaDummy002 A B R p) from (by
                          unfold nb082AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0005 A B R p) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
                    [((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
                      ((nb082AlphaDummy000 A B R), p),
                      ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
                    (synCxpk B B) (nb082WppRefl0007 A B R p dv_B_p)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                            (freshVar_injective (((synCin
                                  (synCimak (synCcnvk (synCfdminsep R A B))
                                    (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
                                  (synC1c))).fv) (by decide)) (freshVar_injective (((synCin
                                  (synCimak (synCcnvk (synCfdminsep R A B))
                                    (synCsn (Class.cv p))) (synC1c))).fv) (by decide))
                            (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb082SplitAlpha0003 A B R p dv_A_p dv_B_p
                                  dv_R_p))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
