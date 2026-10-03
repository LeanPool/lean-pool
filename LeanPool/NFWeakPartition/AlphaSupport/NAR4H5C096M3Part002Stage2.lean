/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C096M3Part002Stage1


/-! NF weak partition development: NAR4H5C096M3Part002. -/


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
noncomputable def nb096_split_alpha_0000 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_035 D R))
          (Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb096_alpha_dummy_036 D R q))
          (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
              (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_006 D R) from (by
                      unfold nb096_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
                  (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_008 D R q) from (by
                      unfold nb096_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
                  (TAlphaVar.there
                    (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_005 D R) from (by
                        unfold nb096_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
                    (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_007 D R q) from (by
                        unfold nb096_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
                    (TAlphaVar.there
                      (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_035 D R) from (by
                          unfold nb096_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0038 D R) 0))))
                      (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_036 D R q) from
                        (by
                          unfold nb096_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0039 D R q) 0))))
                      (TAlphaVar.there
                        (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_009 D R) from (by
                            unfold nb096_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0035 D R) 0)))) (show
                          (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_010 D R q) from (by
                            unfold nb096_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0037 D R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
                      ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_013 D R) from (by
          unfold nb096_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_015 D R q) from (by
          unfold nb096_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_006 D R) ≠ (nb096_alpha_dummy_014 D R) from (by
          unfold nb096_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_016 D R q) from (by
          unfold nb096_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_039 D R) from (by
          unfold nb096_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_040 D R q) from
        (by
          unfold nb096_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_037 D R) from (by
          unfold nb096_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_038 D R q) from
        (by
          unfold nb096_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D
        R) ≠ (nb096_alpha_dummy_020 D R) from (by
          unfold
            nb096_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_023 D R q) from
        (by
          unfold
            nb096_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_019 D R) from (by
          unfold
            nb096_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_022 D R q) from
        (by
          unfold
            nb096_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold
            nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold
            nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D
        R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D
        R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D
        R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D
        R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from
        (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020
        D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018
        D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039
        D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008
        D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009
        D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠ (nb096_alpha_dummy_033 D R) from
        (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_033 D R) from (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_013 D R) from (by
          unfold nb096_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_015 D R q) from (by
          unfold nb096_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_006 D R) ≠ (nb096_alpha_dummy_014 D R) from (by
          unfold nb096_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_016 D R q) from (by
          unfold nb096_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_039 D R) from (by
          unfold nb096_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_040 D R q) from
        (by
          unfold nb096_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_037 D R) from (by
          unfold nb096_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_038 D R q) from
        (by
          unfold nb096_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D
        R) ≠ (nb096_alpha_dummy_020 D R) from (by
          unfold
            nb096_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_023 D R q) from
        (by
          unfold
            nb096_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_019 D R) from (by
          unfold
            nb096_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_022 D R q) from
        (by
          unfold
            nb096_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold
            nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold
            nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D
        R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D
        R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D
        R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D
        R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from
        (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020
        D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018
        D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039
        D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008
        D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009
        D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠ (nb096_alpha_dummy_033 D R) from
        (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_033 D R) from (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
                          ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
                          ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
                          ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
                          ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
                          ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                          ((nb096_alpha_dummy_000 D R), q),
                          ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

@[expose]
noncomputable def nb096_split_alpha_0001 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_035 D R))
          (Class.cab (nb096_alpha_dummy_005 D R)
            (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_035 D R))
            (Class.cab (nb096_alpha_dummy_005 D R)
              (syn_wrex (nb096_alpha_dummy_006 D R) (Class.cv (nb096_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_036 D R q))
          (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
              (Class.cv (nb096_alpha_dummy_002 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_036 D R q))
            (Class.cab (nb096_alpha_dummy_007 D R q) (syn_wrex (nb096_alpha_dummy_008 D R q)
                (Class.cv (nb096_alpha_dummy_002 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_007 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_008 D R q)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_006 D R) from (by
                      unfold nb096_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
                  (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_008 D R q) from (by
                      unfold nb096_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
                  (TAlphaVar.there
                    (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_005 D R) from (by
                        unfold nb096_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
                    (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_007 D R q) from (by
                        unfold nb096_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
                    (TAlphaVar.there
                      (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_035 D R) from (by
                          unfold nb096_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0038 D R) 0))))
                      (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_036 D R q) from
                        (by
                          unfold nb096_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0039 D R q) 0))))
                      (TAlphaVar.there
                        (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_009 D R) from (by
                            unfold nb096_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0035 D R) 0)))) (show
                          (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_010 D R q) from (by
                            unfold nb096_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0037 D R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
                      ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv q)).fv ∪ ((Class.cv (nb096_alpha_dummy_002 D R q))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_013 D R) from (by
          unfold nb096_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_015 D R q) from (by
          unfold nb096_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_006 D R) ≠ (nb096_alpha_dummy_014 D R) from (by
          unfold nb096_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_016 D R q) from (by
          unfold nb096_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_039 D R) from (by
          unfold nb096_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_040 D R q) from
        (by
          unfold nb096_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_037 D R) from (by
          unfold nb096_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_038 D R q) from
        (by
          unfold nb096_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D
        R) ≠ (nb096_alpha_dummy_020 D R) from (by
          unfold
            nb096_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_023 D R q) from
        (by
          unfold
            nb096_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_019 D R) from (by
          unfold
            nb096_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_022 D R q) from
        (by
          unfold
            nb096_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold
            nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold
            nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D
        R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D
        R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D
        R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D
        R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from
        (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020
        D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018
        D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039
        D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008
        D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009
        D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠ (nb096_alpha_dummy_033 D R) from
        (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_033 D R) from (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_013 D R) from (by
          unfold nb096_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_015 D R q) from (by
          unfold nb096_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_006 D R) ≠ (nb096_alpha_dummy_014 D R) from (by
          unfold nb096_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_016 D R q) from (by
          unfold nb096_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_039 D R) from (by
          unfold nb096_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_040 D R q) from
        (by
          unfold nb096_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_037 D R) from (by
          unfold nb096_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096_alpha_dummy_008 D R q) ≠ (nb096_alpha_dummy_038 D R q) from
        (by
          unfold nb096_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D
        R) ≠ (nb096_alpha_dummy_020 D R) from (by
          unfold
            nb096_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_023 D R q) from
        (by
          unfold
            nb096_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_019 D R) from (by
          unfold
            nb096_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_022 D R q) from
        (by
          unfold
            nb096_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold
            nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold
            nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D
        R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039 D
        R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D
        R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009 D
        R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from
        (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020
        D R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018
        D R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_039
        D R), (nb096_alpha_dummy_040 D R q)), ((nb096_alpha_dummy_037 D R),
        (nb096_alpha_dummy_038 D R q)), ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008
        D R q)), ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)), ((nb096_alpha_dummy_009
        D R), (nb096_alpha_dummy_010 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠ (nb096_alpha_dummy_033 D R) from
        (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_033 D R) from (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_039 D R), (nb096_alpha_dummy_040 D R q)),
        ((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb096_alpha_dummy_037 D R), (nb096_alpha_dummy_038 D R q)),
                          ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
                          ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
                          ((nb096_alpha_dummy_035 D R), (nb096_alpha_dummy_036 D R q)),
                          ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
                          ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                          ((nb096_alpha_dummy_000 D R), q),
                          ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb096_split_alpha_0000 D R q))


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
noncomputable def nb096_split_alpha_0002 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.classEq (Class.cv (nb096_alpha_dummy_003 D R))
        (syn_cop (Class.cv (nb096_alpha_dummy_000 D R)) (Class.cv (nb096_alpha_dummy_001 D R))))
      (Wff.classEq (Class.cv (nb096_alpha_dummy_004 D R q))
        (syn_cop (Class.cv q) (Class.cv (nb096_alpha_dummy_002 D R q)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb096_alpha_dummy_001 D R) ≠ (nb096_alpha_dummy_003 D R) from (by
              unfold nb096_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0002 D R) 0)))))
        (Ne.symm (show (nb096_alpha_dummy_002 D R q) ≠ (nb096_alpha_dummy_004 D R q) from (by
              unfold nb096_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0003 D R q) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_003 D R) from (by
                unfold nb096_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0000 D R) 0)))))
          (Ne.symm (show q ≠ (nb096_alpha_dummy_004 D R q) from (by
                unfold nb096_alpha_dummy_004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0001 D R q) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
                                    (nb096_alpha_dummy_006 D R) from (by
                                    unfold nb096_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                            1)))) (show q ≠ (nb096_alpha_dummy_008 D R q) from
                                  (by
                                    unfold nb096_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0008 D R q)
                                            1)))) (TAlphaVar.there (show
                                    (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_005 D R)
                                    from (by
                                      unfold nb096_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                              0)))) (show q ≠ (nb096_alpha_dummy_007 D R q) from
                                    (by
                                      unfold nb096_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0008 D R q) 0))))
                                  (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
                                        (nb096_alpha_dummy_011 D R) from (by
                                        unfold nb096_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0010 D R) 0))))
                                    (show q ≠ (nb096_alpha_dummy_012 D R q) from (by
                                        unfold nb096_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0011 D R q) 0))))
                                    (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_009 D R) from (by
                                          unfold nb096_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0007 D R) 0))))
                                      (show q ≠ (nb096_alpha_dummy_010 D R q) from (by
                                          unfold nb096_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0009 D R q) 0))))
                                      (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_001 D R) from (by
          unfold nb096_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004 D R) 0))))
                                        (show q ≠ (nb096_alpha_dummy_002 D R q) from (by
          unfold nb096_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0005 D R q) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
                                    ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv q)).fv ∪
                                    ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_013 D R) from (by
          unfold nb096_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_015 D R q) from (by
          unfold nb096_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_006 D R) ≠ (nb096_alpha_dummy_014 D R) from (by
          unfold nb096_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_016 D R q) from (by
          unfold nb096_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_013 D R) ≠ (nb096_alpha_dummy_020 D R) from (by
          unfold
            nb096_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_023 D R q) from
        (by
          unfold
            nb096_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_019 D R) from (by
          unfold
            nb096_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_022 D R q) from
        (by
          unfold
            nb096_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold
            nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold
            nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R
        q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D
        R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R),
        (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R
        q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D
        R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from
        (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D
        R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D
        R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R),
        (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D
        R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D
        R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠ (nb096_alpha_dummy_033 D R) from
        (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_033 D R) from (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_013 D R) ≠ (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
                                    (nb096_alpha_dummy_006 D R) from (by
                                    unfold nb096_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                            1)))) (show q ≠ (nb096_alpha_dummy_008 D R q) from
                                  (by
                                    unfold nb096_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0008 D R q)
                                            1)))) (TAlphaVar.there (show
                                    (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_005 D R)
                                    from (by
                                      unfold nb096_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                              0)))) (show q ≠ (nb096_alpha_dummy_007 D R q) from
                                    (by
                                      unfold nb096_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0008 D R q) 0))))
                                  (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
                                        (nb096_alpha_dummy_011 D R) from (by
                                        unfold nb096_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0010 D R) 0))))
                                    (show q ≠ (nb096_alpha_dummy_012 D R q) from (by
                                        unfold nb096_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0011 D R q) 0))))
                                    (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_009 D R) from (by
                                          unfold nb096_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0007 D R) 0))))
                                      (show q ≠ (nb096_alpha_dummy_010 D R q) from (by
                                          unfold nb096_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0009 D R q) 0))))
                                      (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_001 D R) from (by
          unfold nb096_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004 D R) 0))))
                                        (show q ≠ (nb096_alpha_dummy_002 D R q) from (by
          unfold nb096_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0005 D R q) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb096_alpha_dummy_000 D R))).fv ∪
                                    ((Class.cv (nb096_alpha_dummy_001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv q)).fv ∪
                                    ((Class.cv (nb096_alpha_dummy_002 D R q))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb096_alpha_dummy_006 D R) ≠
        (nb096_alpha_dummy_013 D R) from (by
          unfold nb096_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_015 D R q) from (by
          unfold nb096_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_006 D R) ≠ (nb096_alpha_dummy_014 D R) from (by
          unfold nb096_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096_alpha_dummy_008 D R q) ≠
        (nb096_alpha_dummy_016 D R q) from (by
          unfold nb096_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_013 D R) ≠ (nb096_alpha_dummy_020 D R) from (by
          unfold
            nb096_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_023 D R q) from
        (by
          unfold
            nb096_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_019 D R) from (by
          unfold
            nb096_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_022 D R q) from
        (by
          unfold
            nb096_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold
            nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold
            nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R
        q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D
        R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R),
        (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R
        q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D
        R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠ (nb096_alpha_dummy_027 D R) from
        (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_027 D R) from (by
          unfold
            nb096_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_028 D R q) from
        (by
          unfold
            nb096_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_025 D R) from (by
          unfold
            nb096_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_026 D R q) from
        (by
          unfold
            nb096_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_021 D R), (nb096_alpha_dummy_024 D R q)), ((nb096_alpha_dummy_020 D
        R), (nb096_alpha_dummy_023 D R q)), ((nb096_alpha_dummy_019 D R),
        (nb096_alpha_dummy_022 D R q)), ((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D
        R q)), ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)), ((nb096_alpha_dummy_006 D
        R), (nb096_alpha_dummy_008 D R q)), ((nb096_alpha_dummy_005 D R),
        (nb096_alpha_dummy_007 D R q)), ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D
        R q)), ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D
        R), q), ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_020 D
        R) ≠ (nb096_alpha_dummy_031 D R) from (by
          unfold
            nb096_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_032 D R q) from
        (by
          unfold
            nb096_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_020 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_023 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_015 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠ (nb096_alpha_dummy_033 D R) from
        (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_021 D
        R) ≠ (nb096_alpha_dummy_033 D R) from (by
          unfold
            nb096_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_034 D R q) from
        (by
          unfold
            nb096_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_021 D R) ≠
        (nb096_alpha_dummy_029 D R) from (by
          unfold
            nb096_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_024 D R q) ≠ (nb096_alpha_dummy_030 D R q) from
        (by
          unfold
            nb096_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_013 D R) ≠ (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_013 D R) ≠
        (nb096_alpha_dummy_017 D R) from (by
          unfold nb096_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096_alpha_dummy_015 D R q) ≠ (nb096_alpha_dummy_018 D R q) from
        (by
          unfold nb096_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_017 D R), (nb096_alpha_dummy_018 D R q)),
        ((nb096_alpha_dummy_013 D R), (nb096_alpha_dummy_015 D R q)),
        ((nb096_alpha_dummy_014 D R), (nb096_alpha_dummy_016 D R q)),
        ((nb096_alpha_dummy_006 D R), (nb096_alpha_dummy_008 D R q)),
        ((nb096_alpha_dummy_005 D R), (nb096_alpha_dummy_007 D R q)),
        ((nb096_alpha_dummy_011 D R), (nb096_alpha_dummy_012 D R q)),
        ((nb096_alpha_dummy_009 D R), (nb096_alpha_dummy_010 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0001 D R q)))))))))

theorem nb096_focused_notmem_0000 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0106 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_cpw1] using (nb096_focused_notmem_0000 D R)

theorem nb096_focused_notmem_0001 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0107 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_cpw1] using (nb096_focused_notmem_0001 D R q)

theorem nb096_focused_notmem_0002 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb096_wpp_notmem_0108 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_cpw1] using (nb096_focused_notmem_0002 D R)

theorem nb096_wpp_notmem_0109 (D : Class) (q : Var) (dv_D_q : q ∉ D.fv) :
    q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by simpa only [fv_syn_cpw1] using dv_D_q

theorem nb096_focused_notmem_0003 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪
            ({(nb096_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                          (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb096_alpha_dummy_001 D R)) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb096_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0110 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_cpw1] using (nb096_focused_notmem_0003 D R)

theorem nb096_focused_notmem_0004 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0111 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_cpw1] using (nb096_focused_notmem_0004 D R q)

theorem nb096_compact_envfresh_0007 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TEnvFresh
      [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      ((syn_cpw1 (syn_cpw1 D))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q)
      (nb096_wpp_notmem_0106 D R) (nb096_wpp_notmem_0107 D R q)
      (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0108 D R)
        (nb096_wpp_notmem_0109 D q dv_D_q)
        (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q)
          (nb096_wpp_notmem_0110 D R) (nb096_wpp_notmem_0111 D R q)
          (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 D))).fv))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
