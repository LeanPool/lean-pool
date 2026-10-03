/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C070C001Part004Stage1


/-! NF weak partition development: NAR4C070C001Part004. -/


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
noncomputable def nb070_wpp_refl_0010 (x : Var) (A : Class) (b : Var) :
    TReflOn
      [((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      ((syn_cen)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0010 x A b)

@[expose]
noncomputable def nb070_split_alpha_0006 (x : Var) (A : Class) (b : Var)
    (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_b_x : b ≠ x) :
    TAlphaWff
      [((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.imp (Wff.objMem (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_005 A)) (Wff.neg
          (Wff.classMem (Class.cv (nb070_alpha_dummy_005 A))
            (Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq
                (Class.cab (nb070_alpha_dummy_000 A)
                  (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                    (syn_wrex (nb070_alpha_dummy_001 A) A
                      (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                        (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
                (syn_csn (Class.cv (nb070_alpha_dummy_002 A))))))))
      (Wff.imp (Wff.objMem (nb070_alpha_dummy_006 x A b) (nb070_alpha_dummy_007 x A b)) (Wff.neg
          (Wff.classMem (Class.cv (nb070_alpha_dummy_007 x A b))
            (Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
                  (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                      (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
                (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))))) :=
  (TAlphaWff.imp (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
          (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq
                (Class.cab (nb070_alpha_dummy_000 A)
                  (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                    (syn_wrex (nb070_alpha_dummy_001 A) A
                      (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                        (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
                (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) (by decide))
        (freshVar_injective (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
                  (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                      (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
                (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) (by decide))
        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_000 A), b),
                      ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                      ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                      ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                    (syn_cncs) (nb070_wpp_refl_0000 x A b))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                          ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                          ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                          ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                        A (nb070_wpp_refl_0001 x A b dv_A_b dv_A_x))) (TAlphaWff.classEq
                      (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_b_x
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg
                                      (TAlphaWff.neg (nb070_split_alpha_0000 x A b)))))))
                            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb070_alpha_dummy_009 A) ≠ (nb070_alpha_dummy_025 A) from (by
          unfold
            nb070_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  1)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_027 x) from (by
          unfold
            nb070_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  1)))) (TAlphaVar.there (show (nb070_alpha_dummy_009 A) ≠
        (nb070_alpha_dummy_024 A) from (by
          unfold
            nb070_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  0)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_026 x) from (by
          unfold
            nb070_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  0)))) (TAlphaVar.there (show (nb070_alpha_dummy_009 A) ≠
        (nb070_alpha_dummy_030 A) from (by
          unfold
            nb070_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0022
                    A)
                  0)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_031 x) from (by
          unfold
            nb070_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0023
                    x)
                  0)))) (TAlphaVar.there (show (nb070_alpha_dummy_009 A) ≠
        (nb070_alpha_dummy_028 A) from (by
          unfold
            nb070_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0019
                    A)
                  0)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_029 x) from (by
          unfold
            nb070_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0021
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb070_split_alpha_0002 x A b)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb070_alpha_dummy_009 A) ≠ (nb070_alpha_dummy_025 A) from (by
          unfold
            nb070_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  1)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_027 x) from (by
          unfold
            nb070_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  1)))) (TAlphaVar.there (show (nb070_alpha_dummy_009 A) ≠
        (nb070_alpha_dummy_024 A) from (by
          unfold
            nb070_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  0)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_026 x) from (by
          unfold
            nb070_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  0)))) (TAlphaVar.there (show (nb070_alpha_dummy_009 A) ≠
        (nb070_alpha_dummy_030 A) from (by
          unfold
            nb070_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0022
                    A)
                  0)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_031 x) from (by
          unfold
            nb070_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0023
                    x)
                  0)))) (TAlphaVar.there (show (nb070_alpha_dummy_009 A) ≠
        (nb070_alpha_dummy_028 A) from (by
          unfold
            nb070_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0019
                    A)
                  0)))) (show (nb070_alpha_dummy_011 x) ≠ (nb070_alpha_dummy_029 x) from (by
          unfold
            nb070_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0021
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb070_split_alpha_0002 x A b)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb070_split_alpha_0005 x A b)))))))) (TAlphaClass.refl_of_reflOn
                                [((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                                  ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                                  ((nb070_alpha_dummy_001 A), x),
                                  ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A),
                                    (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A),
                                    (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A),
                                    (nb070_alpha_dummy_006 x A b))]
                                (syn_cen) (nb070_wpp_refl_0010 x A b))))))))))) (TAlphaClass.cab
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb070_alpha_dummy_002 A) ≠ (nb070_alpha_dummy_060 A) from (by
                        unfold nb070_alpha_dummy_060;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0056 A) 0))))
                    (show (nb070_alpha_dummy_003 x A b) ≠ (nb070_alpha_dummy_061 x A b) from (by
                        unfold nb070_alpha_dummy_061;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0057 x A b) 0))))
                    (TAlphaVar.here _ _ _))))))))))

@[expose]
noncomputable def nominal_df_tc (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_b_x : b ≠ x) :
    Nominal.NPrf
      (.classEq (syn_ctc A) (syn_cio b (syn_wa (.classMem (.cv b) (syn_cncs))
            (syn_wrex x A (.classEq (.cv b) (syn_cnc (syn_cpw1 (.cv x)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex
          (TAlphaWff.neg (nb070_split_alpha_0006 x A b dv_A_b dv_A_x dv_b_x))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
