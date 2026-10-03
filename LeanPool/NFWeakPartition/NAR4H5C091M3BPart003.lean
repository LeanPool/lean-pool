/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart002

/-! NF weak partition development: NAR4H5C091M3BPart003. -/


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
noncomputable def nb091_split_alpha_0000 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.neg (Wff.classMem (Class.cv (nb091_alpha_dummy_035 D R))
          (Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb091_alpha_dummy_036 D R p))
          (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
              (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_006 D R) from (by
                      unfold nb091_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
                  (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_008 D R p) from (by
                      unfold nb091_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_005 D R) from (by
                        unfold nb091_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
                    (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_007 D R p) from (by
                        unfold nb091_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_035 D R) from (by
                          unfold nb091_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0038 D R) 0))))
                      (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_036 D R p) from
                        (by
                          unfold nb091_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0039 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_009 D R) from (by
                            unfold nb091_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0035 D R) 0)))) (show
                          (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_010 D R p) from (by
                            unfold nb091_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0037 D R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_013 D R) from (by
          unfold nb091_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_015 D R p) from (by
          unfold nb091_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_006 D R) ≠ (nb091_alpha_dummy_014 D R) from (by
          unfold nb091_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_016 D R p) from (by
          unfold nb091_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_039 D R) from (by
          unfold nb091_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_040 D R p) from
        (by
          unfold nb091_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_037 D R) from (by
          unfold nb091_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_038 D R p) from
        (by
          unfold nb091_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D
        R) ≠ (nb091_alpha_dummy_020 D R) from (by
          unfold
            nb091_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_023 D R p) from
        (by
          unfold
            nb091_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_019 D R) from (by
          unfold
            nb091_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_022 D R p) from
        (by
          unfold
            nb091_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold
            nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold
            nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D
        R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039 D
        R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D
        R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009 D
        R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from
        (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020
        D R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018
        D R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039
        D R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008
        D R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009
        D R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠ (nb091_alpha_dummy_033 D R) from
        (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_033 D R) from (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_013 D R) from (by
          unfold nb091_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_015 D R p) from (by
          unfold nb091_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_006 D R) ≠ (nb091_alpha_dummy_014 D R) from (by
          unfold nb091_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_016 D R p) from (by
          unfold nb091_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_039 D R) from (by
          unfold nb091_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_040 D R p) from
        (by
          unfold nb091_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_037 D R) from (by
          unfold nb091_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_038 D R p) from
        (by
          unfold nb091_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D
        R) ≠ (nb091_alpha_dummy_020 D R) from (by
          unfold
            nb091_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_023 D R p) from
        (by
          unfold
            nb091_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_019 D R) from (by
          unfold
            nb091_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_022 D R p) from
        (by
          unfold
            nb091_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold
            nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold
            nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D
        R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039 D
        R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D
        R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009 D
        R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from
        (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020
        D R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018
        D R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039
        D R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008
        D R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009
        D R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠ (nb091_alpha_dummy_033 D R) from
        (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_033 D R) from (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
                          ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
                          ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
                          ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
                          ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
                          ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                          ((nb091_alpha_dummy_000 D R), p),
                          ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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
noncomputable def nb091_split_alpha_0001 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_035 D R))
          (Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_035 D R))
            (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_036 D R p))
          (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
              (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_036 D R p))
            (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
                (Class.cv (nb091_alpha_dummy_002 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_006 D R) from (by
                      unfold nb091_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
                  (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_008 D R p) from (by
                      unfold nb091_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_005 D R) from (by
                        unfold nb091_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
                    (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_007 D R p) from (by
                        unfold nb091_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_035 D R) from (by
                          unfold nb091_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0038 D R) 0))))
                      (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_036 D R p) from
                        (by
                          unfold nb091_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0039 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_009 D R) from (by
                            unfold nb091_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0035 D R) 0)))) (show
                          (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_010 D R p) from (by
                            unfold nb091_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0037 D R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_013 D R) from (by
          unfold nb091_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_015 D R p) from (by
          unfold nb091_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_006 D R) ≠ (nb091_alpha_dummy_014 D R) from (by
          unfold nb091_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_016 D R p) from (by
          unfold nb091_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_039 D R) from (by
          unfold nb091_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_040 D R p) from
        (by
          unfold nb091_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_037 D R) from (by
          unfold nb091_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_038 D R p) from
        (by
          unfold nb091_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D
        R) ≠ (nb091_alpha_dummy_020 D R) from (by
          unfold
            nb091_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_023 D R p) from
        (by
          unfold
            nb091_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_019 D R) from (by
          unfold
            nb091_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_022 D R p) from
        (by
          unfold
            nb091_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold
            nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold
            nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D
        R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039 D
        R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D
        R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009 D
        R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from
        (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020
        D R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018
        D R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039
        D R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008
        D R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009
        D R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠ (nb091_alpha_dummy_033 D R) from
        (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_033 D R) from (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_013 D R) from (by
          unfold nb091_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_015 D R p) from (by
          unfold nb091_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_006 D R) ≠ (nb091_alpha_dummy_014 D R) from (by
          unfold nb091_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_016 D R p) from (by
          unfold nb091_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_039 D R) from (by
          unfold nb091_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_040 D R p) from
        (by
          unfold nb091_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_037 D R) from (by
          unfold nb091_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091_alpha_dummy_008 D R p) ≠ (nb091_alpha_dummy_038 D R p) from
        (by
          unfold nb091_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D
        R) ≠ (nb091_alpha_dummy_020 D R) from (by
          unfold
            nb091_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_023 D R p) from
        (by
          unfold
            nb091_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_019 D R) from (by
          unfold
            nb091_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_022 D R p) from
        (by
          unfold
            nb091_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold
            nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold
            nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D
        R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039 D
        R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D
        R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009 D
        R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from
        (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020
        D R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018
        D R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_039
        D R), (nb091_alpha_dummy_040 D R p)), ((nb091_alpha_dummy_037 D R),
        (nb091_alpha_dummy_038 D R p)), ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008
        D R p)), ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)), ((nb091_alpha_dummy_009
        D R), (nb091_alpha_dummy_010 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠ (nb091_alpha_dummy_033 D R) from
        (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_033 D R) from (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_039 D R), (nb091_alpha_dummy_040 D R p)),
        ((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb091_alpha_dummy_037 D R), (nb091_alpha_dummy_038 D R p)),
                          ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
                          ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
                          ((nb091_alpha_dummy_035 D R), (nb091_alpha_dummy_036 D R p)),
                          ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
                          ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                          ((nb091_alpha_dummy_000 D R), p),
                          ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb091_split_alpha_0000 D R p))

@[expose]
noncomputable def nb091_split_alpha_0002 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.classEq (Class.cv (nb091_alpha_dummy_003 D R))
        (syn_cop (Class.cv (nb091_alpha_dummy_000 D R)) (Class.cv (nb091_alpha_dummy_001 D R))))
      (Wff.classEq (Class.cv (nb091_alpha_dummy_004 D R p))
        (syn_cop (Class.cv p) (Class.cv (nb091_alpha_dummy_002 D R p)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_003 D R) from (by
              unfold nb091_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0002 D R) 0)))))
        (Ne.symm (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_004 D R p) from (by
              unfold nb091_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0003 D R p) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_003 D R) from (by
                unfold nb091_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0000 D R) 0)))))
          (Ne.symm (show p ≠ (nb091_alpha_dummy_004 D R p) from (by
                unfold nb091_alpha_dummy_004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0001 D R p) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
                                    (nb091_alpha_dummy_006 D R) from (by
                                    unfold nb091_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                            1)))) (show p ≠ (nb091_alpha_dummy_008 D R p) from
                                  (by
                                    unfold nb091_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0008 D R p)
                                            1)))) (TAlphaVar.there (show
                                    (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_005 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                              0)))) (show p ≠ (nb091_alpha_dummy_007 D R p) from
                                    (by
                                      unfold nb091_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0008 D R p) 0))))
                                  (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
                                        (nb091_alpha_dummy_011 D R) from (by
                                        unfold nb091_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0010 D R) 0))))
                                    (show p ≠ (nb091_alpha_dummy_012 D R p) from (by
                                        unfold nb091_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0011 D R p) 0))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_009 D R) from (by
                                          unfold nb091_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0007 D R) 0))))
                                      (show p ≠ (nb091_alpha_dummy_010 D R p) from (by
                                          unfold nb091_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0009 D R p) 0))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_001 D R) from (by
          unfold nb091_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004 D R) 0))))
                                        (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
          unfold nb091_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005 D R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
                                    ((Class.cv (nb091_alpha_dummy_001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_013 D R) from (by
          unfold nb091_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_015 D R p) from (by
          unfold nb091_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_006 D R) ≠ (nb091_alpha_dummy_014 D R) from (by
          unfold nb091_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_016 D R p) from (by
          unfold nb091_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_013 D R) ≠ (nb091_alpha_dummy_020 D R) from (by
          unfold
            nb091_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_023 D R p) from
        (by
          unfold
            nb091_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_019 D R) from (by
          unfold
            nb091_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_022 D R p) from
        (by
          unfold
            nb091_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold
            nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold
            nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R
        p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_006 D
        R), (nb091_alpha_dummy_008 D R p)), ((nb091_alpha_dummy_005 D R),
        (nb091_alpha_dummy_007 D R p)), ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D R
        p)), ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D
        R), p), ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from
        (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D
        R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_006 D
        R), (nb091_alpha_dummy_008 D R p)), ((nb091_alpha_dummy_005 D R),
        (nb091_alpha_dummy_007 D R p)), ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D
        R p)), ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D
        R), p), ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠ (nb091_alpha_dummy_033 D R) from
        (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_033 D R) from (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_013 D R) ≠ (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
                                    (nb091_alpha_dummy_006 D R) from (by
                                    unfold nb091_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                            1)))) (show p ≠ (nb091_alpha_dummy_008 D R p) from
                                  (by
                                    unfold nb091_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0008 D R p)
                                            1)))) (TAlphaVar.there (show
                                    (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_005 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                              0)))) (show p ≠ (nb091_alpha_dummy_007 D R p) from
                                    (by
                                      unfold nb091_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0008 D R p) 0))))
                                  (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
                                        (nb091_alpha_dummy_011 D R) from (by
                                        unfold nb091_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0010 D R) 0))))
                                    (show p ≠ (nb091_alpha_dummy_012 D R p) from (by
                                        unfold nb091_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0011 D R p) 0))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_009 D R) from (by
                                          unfold nb091_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0007 D R) 0))))
                                      (show p ≠ (nb091_alpha_dummy_010 D R p) from (by
                                          unfold nb091_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0009 D R p) 0))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_001 D R) from (by
          unfold nb091_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004 D R) 0))))
                                        (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
          unfold nb091_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005 D R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
                                    ((Class.cv (nb091_alpha_dummy_001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091_alpha_dummy_006 D R) ≠
        (nb091_alpha_dummy_013 D R) from (by
          unfold nb091_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_015 D R p) from (by
          unfold nb091_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_006 D R) ≠ (nb091_alpha_dummy_014 D R) from (by
          unfold nb091_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091_alpha_dummy_008 D R p) ≠
        (nb091_alpha_dummy_016 D R p) from (by
          unfold nb091_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_013 D R) ≠ (nb091_alpha_dummy_020 D R) from (by
          unfold
            nb091_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_023 D R p) from
        (by
          unfold
            nb091_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_019 D R) from (by
          unfold
            nb091_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_022 D R p) from
        (by
          unfold
            nb091_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold
            nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold
            nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R
        p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_006 D
        R), (nb091_alpha_dummy_008 D R p)), ((nb091_alpha_dummy_005 D R),
        (nb091_alpha_dummy_007 D R p)), ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D R
        p)), ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D
        R), p), ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠ (nb091_alpha_dummy_027 D R) from
        (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_027 D R) from (by
          unfold
            nb091_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_028 D R p) from
        (by
          unfold
            nb091_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_025 D R) from (by
          unfold
            nb091_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_026 D R p) from
        (by
          unfold
            nb091_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_021 D R), (nb091_alpha_dummy_024 D R p)), ((nb091_alpha_dummy_020 D
        R), (nb091_alpha_dummy_023 D R p)), ((nb091_alpha_dummy_019 D R),
        (nb091_alpha_dummy_022 D R p)), ((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D
        R p)), ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)), ((nb091_alpha_dummy_006 D
        R), (nb091_alpha_dummy_008 D R p)), ((nb091_alpha_dummy_005 D R),
        (nb091_alpha_dummy_007 D R p)), ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D
        R p)), ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D
        R), p), ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_020 D
        R) ≠ (nb091_alpha_dummy_031 D R) from (by
          unfold
            nb091_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_032 D R p) from
        (by
          unfold
            nb091_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_020 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_023 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_013
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠ (nb091_alpha_dummy_033 D R) from
        (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_021 D
        R) ≠ (nb091_alpha_dummy_033 D R) from (by
          unfold
            nb091_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_034 D R p) from
        (by
          unfold
            nb091_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_021 D R) ≠
        (nb091_alpha_dummy_029 D R) from (by
          unfold
            nb091_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_024 D R p) ≠ (nb091_alpha_dummy_030 D R p) from
        (by
          unfold
            nb091_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_013 D R) ≠ (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_013 D R) ≠
        (nb091_alpha_dummy_017 D R) from (by
          unfold nb091_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091_alpha_dummy_015 D R p) ≠ (nb091_alpha_dummy_018 D R p) from
        (by
          unfold nb091_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_017 D R), (nb091_alpha_dummy_018 D R p)),
        ((nb091_alpha_dummy_013 D R), (nb091_alpha_dummy_015 D R p)),
        ((nb091_alpha_dummy_014 D R), (nb091_alpha_dummy_016 D R p)),
        ((nb091_alpha_dummy_006 D R), (nb091_alpha_dummy_008 D R p)),
        ((nb091_alpha_dummy_005 D R), (nb091_alpha_dummy_007 D R p)),
        ((nb091_alpha_dummy_011 D R), (nb091_alpha_dummy_012 D R p)),
        ((nb091_alpha_dummy_009 D R), (nb091_alpha_dummy_010 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0001 D R p)))))))))

theorem nb091_focused_notmem_0000 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cec
              (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
              (syn_chwniso D))).fv)
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

theorem nb091_wpp_notmem_0106 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb091_alpha_dummy_001, fv_syn_cpw1] using (nb091_focused_notmem_0000 D R)

theorem nb091_focused_notmem_0001 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
          ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
              (syn_chwniso D))).fv)
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

theorem nb091_wpp_notmem_0107 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb091_alpha_dummy_002, fv_syn_cpw1] using (nb091_focused_notmem_0001 D R p)

theorem nb091_focused_notmem_0002 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb091_wpp_notmem_0108 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb091_alpha_dummy_000, fv_syn_cpw1] using (nb091_focused_notmem_0002 D R)

theorem nb091_wpp_notmem_0109 (D : Class) (p : Var) (dv_D_p : p ∉ D.fv) :
    p ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by simpa only [fv_syn_cpw1] using dv_D_p

theorem nb091_focused_notmem_0003 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
            ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
                  (syn_chwniso D))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))) (syn_chwniso D)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb091_wpp_notmem_0110 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb091_alpha_dummy_003, fv_syn_cpw1] using (nb091_focused_notmem_0003 D R)

theorem nb091_focused_notmem_0004 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
                (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
                  (syn_chwniso D))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb091_wpp_notmem_0111 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
  simpa only [nb091_alpha_dummy_004, fv_syn_cpw1] using (nb091_focused_notmem_0004 D R p)

theorem nb091_compact_envfresh_0007 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TEnvFresh
      [((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      ((syn_cpw1 (syn_cpw1 D))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091_alpha_dummy_001 D R) (nb091_alpha_dummy_002 D R p)
      (nb091_wpp_notmem_0106 D R) (nb091_wpp_notmem_0107 D R p)
      (TEnvFresh.consFresh (nb091_alpha_dummy_000 D R) p (nb091_wpp_notmem_0108 D R)
        (nb091_wpp_notmem_0109 D p dv_D_p)
        (TEnvFresh.consFresh (nb091_alpha_dummy_003 D R) (nb091_alpha_dummy_004 D R p)
          (nb091_wpp_notmem_0110 D R) (nb091_wpp_notmem_0111 D R p)
          (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 D))).fv))))

@[expose]
noncomputable def nb091_wpp_refl_0007 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TReflOn
      [((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      ((syn_cpw1 (syn_cpw1 D))).fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0007 D R p dv_D_p)

theorem nb091_focused_notmem_0005 (D : Class) (R : Class) :
    (nb091_alpha_dummy_057 D R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0006 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_058 D R p) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb091_focused_notmem_0007 (D : Class) (R : Class) :
    (nb091_alpha_dummy_055 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
          ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0008 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_056 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cnin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0009 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0010 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0011 (D : Class) (R : Class) :
    (nb091_alpha_dummy_047 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0012 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_049 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0013 (D : Class) (R : Class) :
    (nb091_alpha_dummy_053 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv ∪
          ((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091_alpha_dummy_047 D R)
      (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0011 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_048 D R)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0009 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0014 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_054 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv ∪
          ((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091_alpha_dummy_049 D R p)
      (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0012 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_050 D R p)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0010 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0015 (D : Class) (R : Class) :
    (nb091_alpha_dummy_051 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccompl (Class.cab (nb091_alpha_dummy_047 D R)
                (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                              (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                              (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                    (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))))).fv ∪ ((syn_ccompl
              (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                    (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                      (syn_csn (syn_c0c)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
          (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
            (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))]
  rw [fv_class_cab (nb091_alpha_dummy_047 D R)
      (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0011 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_048 D R)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0009 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0016 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_052 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccompl (Class.cab (nb091_alpha_dummy_049 D R p)
                (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                    (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))))).fv ∪ ((syn_ccompl
              (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                    (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                      (syn_csn (syn_c0c)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
          (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
          (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
            (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))]
  rw [fv_class_cab (nb091_alpha_dummy_049 D R p)
      (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0012 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_050 D R p)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0010 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0017 (D : Class) (R : Class) :
    (nb091_alpha_dummy_045 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0018 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_046 D R p) ∉ R.fv :=
  by
  change freshVar (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))).fv) 0 ∉ R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0019 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0020 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪
          ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))]
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0021 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0022 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪
          ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))]
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0023 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cec
              (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
              (syn_chwniso D))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
      (syn_chwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0024 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
          ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
              (syn_chwniso D))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0025 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0026 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
            ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
                  (syn_chwniso D))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))) (syn_chwniso D)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb091_alpha_dummy_001 D R))
      (syn_cec
        (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
        (syn_chwniso D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
      (syn_chwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0027 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
                (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
                  (syn_chwniso D))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb091_alpha_dummy_002 D R p))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_compact_envfresh_0008 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TEnvFresh
      [((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091_alpha_dummy_057 D R) (nb091_alpha_dummy_058 D R p)
      (nb091_focused_notmem_0005 D R) (nb091_focused_notmem_0006 D R p)
      (TEnvFresh.consFresh (nb091_alpha_dummy_055 D R) (nb091_alpha_dummy_056 D R p)
        (nb091_focused_notmem_0007 D R) (nb091_focused_notmem_0008 D R p)
        (TEnvFresh.consFresh (nb091_alpha_dummy_048 D R) (nb091_alpha_dummy_050 D R p)
          (nb091_focused_notmem_0009 D R) (nb091_focused_notmem_0010 D R p)
          (TEnvFresh.consFresh (nb091_alpha_dummy_047 D R) (nb091_alpha_dummy_049 D R p)
            (nb091_focused_notmem_0011 D R) (nb091_focused_notmem_0012 D R p)
            (TEnvFresh.consFresh (nb091_alpha_dummy_053 D R) (nb091_alpha_dummy_054 D R p)
              (nb091_focused_notmem_0013 D R) (nb091_focused_notmem_0014 D R p)
              (TEnvFresh.consFresh (nb091_alpha_dummy_051 D R)
                (nb091_alpha_dummy_052 D R p) (nb091_focused_notmem_0015 D R)
                (nb091_focused_notmem_0016 D R p)
                (TEnvFresh.consFresh (nb091_alpha_dummy_045 D R)
                  (nb091_alpha_dummy_046 D R p) (nb091_focused_notmem_0017 D R)
                  (nb091_focused_notmem_0018 D R p)
                  (TEnvFresh.consFresh (nb091_alpha_dummy_042 D R)
                    (nb091_alpha_dummy_044 D R p) (nb091_focused_notmem_0019 D R)
                    (nb091_focused_notmem_0020 D R p)
                    (TEnvFresh.consFresh (nb091_alpha_dummy_041 D R)
                      (nb091_alpha_dummy_043 D R p) (nb091_focused_notmem_0021 D R)
                      (nb091_focused_notmem_0022 D R p)
                      (TEnvFresh.consFresh (nb091_alpha_dummy_001 D R)
                        (nb091_alpha_dummy_002 D R p) (nb091_focused_notmem_0023 D R)
                        (nb091_focused_notmem_0024 D R p)
                        (TEnvFresh.consFresh (nb091_alpha_dummy_000 D R) p
                          (nb091_focused_notmem_0025 D R) dv_R_p
                          (TEnvFresh.consFresh (nb091_alpha_dummy_003 D R)
                            (nb091_alpha_dummy_004 D R p) (nb091_focused_notmem_0026 D R)
                            (nb091_focused_notmem_0027 D R p) (TEnvFresh.nil R.fv)))))))))))))

@[expose]
noncomputable def nb091_focused_refl_0000 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TReflOn
      [((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      R.fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0008 D R p dv_R_p)

theorem nb091_compact_fv_empty_0052 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0053 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0054 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0055 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0056 (D : Class) (R : Class) :
    (nb091_alpha_dummy_063 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0057 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_064 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0058 (D : Class) (R : Class) :
    (nb091_alpha_dummy_057 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0059 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_058 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0060 (D : Class) (R : Class) :
    (nb091_alpha_dummy_055 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0061 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_056 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0062 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0063 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0064 (D : Class) (R : Class) :
    (nb091_alpha_dummy_047 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0065 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_049 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0066 (D : Class) (R : Class) :
    (nb091_alpha_dummy_053 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0067 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_054 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0068 (D : Class) (R : Class) :
    (nb091_alpha_dummy_051 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0069 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_052 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0070 (D : Class) (R : Class) :
    (nb091_alpha_dummy_045 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0071 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_046 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0072 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0073 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0074 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0075 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
