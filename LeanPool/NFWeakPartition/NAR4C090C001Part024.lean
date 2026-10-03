/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block006

/-! NF weak partition development: NAR4C090C001Part024. -/


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
noncomputable def nb090_split_alpha_0000 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_035 A))
          (Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_035 A))
            (Class.cab (nb090_alpha_dummy_005 A)
              (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_036 v u))
          (Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_036 v u))
            (Class.cab (nb090_alpha_dummy_007 v u)
              (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_006 A) from (by
                      unfold nb090_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
                  (show v ≠ (nb090_alpha_dummy_008 v u) from (by
                      unfold nb090_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0034 v u) 1)))) (TAlphaVar.there
                    (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_005 A) from (by
                        unfold nb090_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
                    (show v ≠ (nb090_alpha_dummy_007 v u) from (by
                        unfold nb090_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_035 A) from (by
                          unfold nb090_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0036 A) 0))))
                      (show v ≠ (nb090_alpha_dummy_036 v u) from (by
                          unfold nb090_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0037 v u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_009 A) from (by
                            unfold nb090_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0033 A) 0))))
                        (show v ≠ (nb090_alpha_dummy_010 v u) from (by
                            unfold nb090_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0035 v u) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_002 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_013 A) from (by
          unfold nb090_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_015 v u) from (by
          unfold nb090_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_014 A) from (by
          unfold nb090_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_016 v u) from (by
          unfold nb090_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_039 A) from (by
          unfold nb090_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_040 v u) from (by
          unfold nb090_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_037 A) from (by
          unfold nb090_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090_alpha_dummy_008 v u) ≠ (nb090_alpha_dummy_038 v u) from (by
          unfold nb090_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_006 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_008 v u))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_020 A) from (by
          unfold
            nb090_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_023 v u) from (by
          unfold
            nb090_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_019 A) from (by
          unfold
            nb090_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_022 v u) from (by
          unfold
            nb090_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold
            nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold
            nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020
        A) ≠ (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_013 A) from (by
          unfold nb090_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_015 v u) from (by
          unfold nb090_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_014 A) from (by
          unfold nb090_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_016 v u) from (by
          unfold nb090_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_039 A) from (by
          unfold nb090_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_040 v u) from (by
          unfold nb090_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_037 A) from (by
          unfold nb090_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090_alpha_dummy_008 v u) ≠ (nb090_alpha_dummy_038 v u) from (by
          unfold nb090_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_006 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_008 v u))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_020 A) from (by
          unfold
            nb090_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_023 v u) from (by
          unfold
            nb090_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_019 A) from (by
          unfold
            nb090_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_022 v u) from (by
          unfold
            nb090_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold
            nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold
            nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020
        A) ≠ (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)),
                          ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
                          ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)),
                          ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)),
                          ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
                          ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
                          ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_006 A) from (by
                        unfold nb090_alpha_dummy_006;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
                    (show v ≠ (nb090_alpha_dummy_008 v u) from (by
                        unfold nb090_alpha_dummy_008;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_005 A) from (by
                          unfold nb090_alpha_dummy_005;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
                      (show v ≠ (nb090_alpha_dummy_007 v u) from (by
                          unfold nb090_alpha_dummy_007;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_035 A) from (by
                            unfold nb090_alpha_dummy_035;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0036 A) 0))))
                        (show v ≠ (nb090_alpha_dummy_036 v u) from (by
                            unfold nb090_alpha_dummy_036;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0037 v u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_009 A) from (by
                              unfold nb090_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0033 A) 0))))
                          (show v ≠ (nb090_alpha_dummy_010 v u) from (by
                              unfold nb090_alpha_dummy_010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0035 v u) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_002 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_013 A) from (by
          unfold nb090_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_015 v u) from (by
          unfold nb090_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_014 A) from (by
          unfold nb090_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_016 v u) from (by
          unfold nb090_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_039 A) from (by
          unfold nb090_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A)
                  0)))) (show (nb090_alpha_dummy_008 v u) ≠ (nb090_alpha_dummy_040 v u) from (by
          unfold nb090_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_037 A) from (by
          unfold nb090_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090_alpha_dummy_008 v u) ≠ (nb090_alpha_dummy_038 v u) from (by
          unfold nb090_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_006 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_008 v u))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013
        A) ≠ (nb090_alpha_dummy_020 A) from (by
          unfold
            nb090_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_023 v u) from (by
          unfold
            nb090_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_019 A) from (by
          unfold
            nb090_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_022 v u) from (by
          unfold
            nb090_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold
            nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold
            nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020
        A) ≠ (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_013 A) from (by
          unfold nb090_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_015 v u) from (by
          unfold nb090_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_014 A) from (by
          unfold nb090_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_016 v u) from (by
          unfold nb090_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_039 A) from (by
          unfold nb090_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A)
                  0)))) (show (nb090_alpha_dummy_008 v u) ≠ (nb090_alpha_dummy_040 v u) from (by
          unfold nb090_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_037 A) from (by
          unfold nb090_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090_alpha_dummy_008 v u) ≠ (nb090_alpha_dummy_038 v u) from (by
          unfold nb090_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_006 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_008 v u))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013
        A) ≠ (nb090_alpha_dummy_020 A) from (by
          unfold
            nb090_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_023 v u) from (by
          unfold
            nb090_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_019 A) from (by
          unfold
            nb090_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_022 v u) from (by
          unfold
            nb090_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold
            nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold
            nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003
        A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020
        A) ≠ (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_039 A), (nb090_alpha_dummy_040 v u)), ((nb090_alpha_dummy_037 A),
        (nb090_alpha_dummy_038 v u)), ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
        ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_035 A),
        (nb090_alpha_dummy_036 v u)), ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_037 A), (nb090_alpha_dummy_038 v u)),
                            ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)),
                            ((nb090_alpha_dummy_005 A), (nb090_alpha_dummy_007 v u)),
                            ((nb090_alpha_dummy_035 A), (nb090_alpha_dummy_036 v u)),
                            ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
                            ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb090_focused_notmem_0000 (A : Class) : (nb090_alpha_dummy_002 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => hu)

theorem nb090_wpp_notmem_0106 (A : Class) :
    (nb090_alpha_dummy_002 A) ∉ ((syn_chwcodes A)).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_chwcodes] using (nb090_focused_notmem_0000 A)

theorem nb090_wpp_notmem_0107 (v : Var) (A : Class) (dv_A_v : v ∉ A.fv) :
    v ∉ ((syn_chwcodes A)).fv := by simpa only [fv_syn_chwcodes] using dv_A_v

theorem nb090_focused_notmem_0001 (A : Class) : (nb090_alpha_dummy_001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => hu)

theorem nb090_wpp_notmem_0108 (A : Class) :
    (nb090_alpha_dummy_001 A) ∉ ((syn_chwcodes A)).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_chwcodes] using (nb090_focused_notmem_0001 A)

theorem nb090_wpp_notmem_0109 (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    u ∉ ((syn_chwcodes A)).fv := by simpa only [fv_syn_chwcodes] using dv_A_u

theorem nb090_focused_notmem_0002 (A : Class) : (nb090_alpha_dummy_003 A) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪
            ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa
              (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
                (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
              (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
                  (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                  (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                  (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
                  (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
        (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
      (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
          (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
          (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_chwcodes A]
  exact hu

theorem nb090_wpp_notmem_0110 (A : Class) :
    (nb090_alpha_dummy_003 A) ∉ ((syn_chwcodes A)).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_chwcodes] using (nb090_focused_notmem_0002 A)

theorem nb090_focused_notmem_0003 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090_alpha_dummy_004 v u A h) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((syn_wa
              (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
                (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
                (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
                  (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
                  (syn_cfv (syn_c2nd) (Class.cv v)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
        (Wff.classMem (Class.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
          (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
          (syn_cfv (syn_c2nd) (Class.cv v))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
      (Wff.classMem (Class.cv v) (syn_chwcodes A))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv u) (syn_chwcodes A)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_chwcodes A]
  exact hu

theorem nb090_wpp_notmem_0111 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090_alpha_dummy_004 v u A h) ∉ ((syn_chwcodes A)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_chwcodes] using
    (nb090_focused_notmem_0003 v u A h)

theorem nb090_compact_envfresh_0007 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    TEnvFresh
      [((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_chwcodes A)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0106 A)
      (nb090_wpp_notmem_0107 v A dv_A_v)
      (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0108 A)
        (nb090_wpp_notmem_0109 u A dv_A_u)
        (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h)
          (nb090_wpp_notmem_0110 A) (nb090_wpp_notmem_0111 v u A h)
          (TEnvFresh.nil ((syn_chwcodes A)).fv))))

@[expose]
noncomputable def nb090_wpp_refl_0007 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    TReflOn
      [((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_chwcodes A)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0007 v u A h dv_A_u dv_A_v)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
