/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C082C001Block001

/-! NF weak partition development: NAR4C082C001Part004. -/


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
noncomputable def nb082_split_alpha_0000 (A : Class) (B : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      (Wff.neg (Wff.classMem (Class.cv (nb082_alpha_dummy_035 A B R))
          (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R)
              (Class.cv (nb082_alpha_dummy_001 A B R))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R))
                (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))
                  (syn_csn (syn_c0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb082_alpha_dummy_036 A B R p))
          (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p)
              (Class.cv (nb082_alpha_dummy_002 A B R p))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p))
                (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_006 A B R) from (by
                      unfold nb082_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))))
                  (show (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_008 A B R p) from
                    (by
                      unfold nb082_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))))
                  (TAlphaVar.there
                    (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_005 A B R) from (by
                        unfold nb082_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0)))) (show
                      (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_007 A B R p) from (by
                        unfold nb082_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))))
                    (TAlphaVar.there
                      (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_035 A B R) from
                        (by
                          unfold nb082_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0038 A B R) 0)))) (show
                        (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_036 A B R p) from
                        (by
                          unfold nb082_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0039 A B R p) 0))))
                      (TAlphaVar.there (show
                          (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_009 A B R) from (by
                            unfold nb082_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0035 A B R) 0)))) (show
                          (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_010 A B R p) from
                          (by
                            unfold nb082_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0037 A B R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪
                      ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_013 A B R) from (by
          unfold nb082_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 0)))) (show (nb082_alpha_dummy_008 A B R p) ≠
        (nb082_alpha_dummy_015 A B R p) from (by
          unfold nb082_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_014 A B R) from (by
          unfold nb082_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_016 A B R p)
        from (by
          unfold nb082_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_039 A B R) from (by
          unfold nb082_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_040 A B R p)
        from (by
          unfold nb082_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_037 A B R) from (by
          unfold nb082_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_038 A B R p)
        from (by
          unfold nb082_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_020 A B R) from (by
          unfold
            nb082_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  1)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_023 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_019 A B R) from (by
          unfold
            nb082_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_022 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold
            nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R)
        from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A
        B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠ (nb082_alpha_dummy_033 A B R)
        from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_033 A B R) from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_013 A B R) from (by
          unfold nb082_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 0)))) (show (nb082_alpha_dummy_008 A B R p) ≠
        (nb082_alpha_dummy_015 A B R p) from (by
          unfold nb082_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_014 A B R) from (by
          unfold nb082_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_016 A B R p)
        from (by
          unfold nb082_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_039 A B R) from (by
          unfold nb082_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_040 A B R p)
        from (by
          unfold nb082_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_037 A B R) from (by
          unfold nb082_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_038 A B R p)
        from (by
          unfold nb082_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_020 A B R) from (by
          unfold
            nb082_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  1)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_023 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_019 A B R) from (by
          unfold
            nb082_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_022 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold
            nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R)
        from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A
        B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠ (nb082_alpha_dummy_033 A B R)
        from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_033 A B R) from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
                          ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
                          ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
                          ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
                          ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
                          ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
                          ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
                            (nb082_alpha_dummy_004 A B R p))] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

@[expose]
noncomputable def nb082_split_alpha_0001 (A : Class) (B : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb082_alpha_dummy_035 A B R))
          (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R)
              (Class.cv (nb082_alpha_dummy_001 A B R))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R))
                (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb082_alpha_dummy_035 A B R))
            (Class.cab (nb082_alpha_dummy_005 A B R) (syn_wrex (nb082_alpha_dummy_006 A B R)
                (Class.cv (nb082_alpha_dummy_001 A B R))
                (Wff.classEq (Class.cv (nb082_alpha_dummy_005 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_006 A B R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb082_alpha_dummy_036 A B R p))
          (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p)
              (Class.cv (nb082_alpha_dummy_002 A B R p))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p))
                (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb082_alpha_dummy_036 A B R p))
            (Class.cab (nb082_alpha_dummy_007 A B R p) (syn_wrex (nb082_alpha_dummy_008 A B R p)
                (Class.cv (nb082_alpha_dummy_002 A B R p))
                (Wff.classEq (Class.cv (nb082_alpha_dummy_007 A B R p))
                  (syn_cun (syn_cphi (Class.cv (nb082_alpha_dummy_008 A B R p)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_006 A B R) from (by
                      unfold nb082_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))))
                  (show (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_008 A B R p) from
                    (by
                      unfold nb082_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))))
                  (TAlphaVar.there
                    (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_005 A B R) from (by
                        unfold nb082_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0)))) (show
                      (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_007 A B R p) from (by
                        unfold nb082_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))))
                    (TAlphaVar.there
                      (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_035 A B R) from
                        (by
                          unfold nb082_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0038 A B R) 0)))) (show
                        (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_036 A B R p) from
                        (by
                          unfold nb082_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0039 A B R p) 0))))
                      (TAlphaVar.there (show
                          (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_009 A B R) from (by
                            unfold nb082_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0035 A B R) 0)))) (show
                          (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_010 A B R p) from
                          (by
                            unfold nb082_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0037 A B R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪
                      ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_013 A B R) from (by
          unfold nb082_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 0)))) (show (nb082_alpha_dummy_008 A B R p) ≠
        (nb082_alpha_dummy_015 A B R p) from (by
          unfold nb082_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_014 A B R) from (by
          unfold nb082_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_016 A B R p)
        from (by
          unfold nb082_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_039 A B R) from (by
          unfold nb082_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_040 A B R p)
        from (by
          unfold nb082_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_037 A B R) from (by
          unfold nb082_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_038 A B R p)
        from (by
          unfold nb082_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_020 A B R) from (by
          unfold
            nb082_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  1)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_023 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_019 A B R) from (by
          unfold
            nb082_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_022 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold
            nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R)
        from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A
        B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠ (nb082_alpha_dummy_033 A B R)
        from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_033 A B R) from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_013 A B R) from (by
          unfold nb082_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 0)))) (show (nb082_alpha_dummy_008 A B R p) ≠
        (nb082_alpha_dummy_015 A B R p) from (by
          unfold nb082_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_014 A B R) from (by
          unfold nb082_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_016 A B R p)
        from (by
          unfold nb082_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_039 A B R) from (by
          unfold nb082_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_040 A B R p)
        from (by
          unfold nb082_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_006 A B R) ≠
        (nb082_alpha_dummy_037 A B R) from (by
          unfold nb082_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082_alpha_dummy_008 A B R p) ≠ (nb082_alpha_dummy_038 A B R p)
        from (by
          unfold nb082_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_020 A B R) from (by
          unfold
            nb082_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  1)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_023 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  1)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_019 A B R) from (by
          unfold
            nb082_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_022 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold
            nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014
                    A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠ (nb082_alpha_dummy_027 A B R)
        from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
          unfold
            nb082_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_028 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_025 A B R) from (by
          unfold
            nb082_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_026 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_021 A B R), (nb082_alpha_dummy_024 A B R p)),
        ((nb082_alpha_dummy_020 A B R), (nb082_alpha_dummy_023 A B R p)),
        ((nb082_alpha_dummy_019 A B R), (nb082_alpha_dummy_022 A B R p)),
        ((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A
        B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
          unfold
            nb082_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_032 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_023 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠ (nb082_alpha_dummy_033 A B R)
        from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021 A
        B R) ≠ (nb082_alpha_dummy_033 A B R) from (by
          unfold
            nb082_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_034 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082_alpha_dummy_021 A B R) ≠
        (nb082_alpha_dummy_029 A B R) from (by
          unfold
            nb082_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082_alpha_dummy_024 A B R p) ≠ (nb082_alpha_dummy_030 A B R p)
        from (by
          unfold
            nb082_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_013 A B R) ≠
        (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_039 A B R), (nb082_alpha_dummy_040 A B R p)),
        ((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb082_alpha_dummy_037 A B R), (nb082_alpha_dummy_038 A B R p)),
                          ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
                          ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
                          ((nb082_alpha_dummy_035 A B R), (nb082_alpha_dummy_036 A B R p)),
                          ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
                          ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
                          ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
                            (nb082_alpha_dummy_004 A B R p))] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb082_split_alpha_0000 A B R p))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
