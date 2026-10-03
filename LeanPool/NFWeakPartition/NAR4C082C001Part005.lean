/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C082C001Part004

/-! NF weak partition development: NAR4C082C001Part005. -/


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
noncomputable def nb082_split_alpha_0002 (A : Class) (B : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      (Wff.classEq (Class.cv (nb082_alpha_dummy_003 A B R))
        (syn_cop (Class.cv (nb082_alpha_dummy_000 A B R))
          (Class.cv (nb082_alpha_dummy_001 A B R))))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_004 A B R p))
        (syn_cop (Class.cv p) (Class.cv (nb082_alpha_dummy_002 A B R p)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb082_alpha_dummy_001 A B R) ≠ (nb082_alpha_dummy_003 A B R) from (by
              unfold nb082_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0002 A B R) 0)))))
        (Ne.symm (show (nb082_alpha_dummy_002 A B R p) ≠ (nb082_alpha_dummy_004 A B R p) from
            (by
              unfold nb082_alpha_dummy_004;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0003 A B R p) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_003 A B R) from (by
                unfold nb082_alpha_dummy_003;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0000 A B R) 0)))))
          (Ne.symm (show p ≠ (nb082_alpha_dummy_004 A B R p) from (by
                unfold nb082_alpha_dummy_004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0001 A B R p) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_006 A B R)
                                  from (by
                                    unfold nb082_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0006 A B R)
                                            1)))) (show p ≠ (nb082_alpha_dummy_008 A B R p) from
                                  (by
                                    unfold nb082_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb082_support_mem_0008 A B R p) 1))))
                                (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                      (nb082_alpha_dummy_005 A B R) from (by
                                      unfold nb082_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0006 A B R) 0))))
                                  (show p ≠ (nb082_alpha_dummy_007 A B R p) from (by
                                      unfold nb082_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0008 A B R p) 0))))
                                  (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                        (nb082_alpha_dummy_011 A B R) from (by
                                        unfold nb082_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0010 A B R) 0))))
                                    (show p ≠ (nb082_alpha_dummy_012 A B R p) from (by
                                        unfold nb082_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0011 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_009 A B R) from (by
                                          unfold nb082_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0007 A B R) 0))))
                                      (show p ≠ (nb082_alpha_dummy_010 A B R p) from (by
                                          unfold nb082_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0009 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_001 A B R) from (by
          unfold nb082_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R) 0))))
                                        (show p ≠ (nb082_alpha_dummy_002 A B R p) from (by
          unfold nb082_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0005 A B R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪
                                    ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb082_support_mem_0013 A B R p) 0)))) (TAlphaVar.there (show
        (nb082_alpha_dummy_006 A B R) ≠ (nb082_alpha_dummy_014 A B R) from (by
          unfold nb082_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 1)))) (show (nb082_alpha_dummy_008 A B R p) ≠
        (nb082_alpha_dummy_016 A B R p) from (by
          unfold nb082_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021
        A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021
        A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
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
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015
        A B R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020
        A B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020
        A B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021
        A B R) ≠ (nb082_alpha_dummy_033 A B R) from (by
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb082_alpha_dummy_000 A B R) ≠ (nb082_alpha_dummy_006 A B R)
                                  from (by
                                    unfold nb082_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0006 A B R)
                                            1)))) (show p ≠ (nb082_alpha_dummy_008 A B R p) from
                                  (by
                                    unfold nb082_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb082_support_mem_0008 A B R p) 1))))
                                (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                      (nb082_alpha_dummy_005 A B R) from (by
                                      unfold nb082_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0006 A B R) 0))))
                                  (show p ≠ (nb082_alpha_dummy_007 A B R p) from (by
                                      unfold nb082_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0008 A B R p) 0))))
                                  (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
                                        (nb082_alpha_dummy_011 A B R) from (by
                                        unfold nb082_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0010 A B R) 0))))
                                    (show p ≠ (nb082_alpha_dummy_012 A B R p) from (by
                                        unfold nb082_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0011 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_009 A B R) from (by
                                          unfold nb082_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0007 A B R) 0))))
                                      (show p ≠ (nb082_alpha_dummy_010 A B R p) from (by
                                          unfold nb082_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0009 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082_alpha_dummy_000 A B R) ≠
        (nb082_alpha_dummy_001 A B R) from (by
          unfold nb082_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R) 0))))
                                        (show p ≠ (nb082_alpha_dummy_002 A B R p) from (by
          unfold nb082_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0005 A B R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb082_alpha_dummy_000 A B R))).fv ∪
                                    ((Class.cv (nb082_alpha_dummy_001 A B R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb082_alpha_dummy_002 A B R p))).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb082_support_mem_0013 A B R p) 0)))) (TAlphaVar.there (show
        (nb082_alpha_dummy_006 A B R) ≠ (nb082_alpha_dummy_014 A B R) from (by
          unfold nb082_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 1)))) (show (nb082_alpha_dummy_008 A B R p) ≠
        (nb082_alpha_dummy_016 A B R p) from (by
          unfold nb082_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_006 A B R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020 A B R) ≠
        (nb082_alpha_dummy_027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021
        A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021
        A B R) ≠ (nb082_alpha_dummy_027 A B R) from (by
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
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082_alpha_dummy_013 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082_alpha_dummy_015 A B R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb082_alpha_dummy_013 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb082_alpha_dummy_015
        A B R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020
        A B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_020
        A B R) ≠ (nb082_alpha_dummy_031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082_alpha_dummy_021
        A B R) ≠ (nb082_alpha_dummy_033 A B R) from (by
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082_alpha_dummy_013 A B R) ≠ (nb082_alpha_dummy_017 A B R) from (by
          unfold nb082_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B R)
                  0)))) (show (nb082_alpha_dummy_015 A B R p) ≠ (nb082_alpha_dummy_018 A B R p)
        from (by
          unfold nb082_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb082_alpha_dummy_017 A B R), (nb082_alpha_dummy_018 A B R p)),
        ((nb082_alpha_dummy_013 A B R), (nb082_alpha_dummy_015 A B R p)),
        ((nb082_alpha_dummy_014 A B R), (nb082_alpha_dummy_016 A B R p)),
        ((nb082_alpha_dummy_006 A B R), (nb082_alpha_dummy_008 A B R p)),
        ((nb082_alpha_dummy_005 A B R), (nb082_alpha_dummy_007 A B R p)),
        ((nb082_alpha_dummy_011 A B R), (nb082_alpha_dummy_012 A B R p)),
        ((nb082_alpha_dummy_009 A B R), (nb082_alpha_dummy_010 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p), ((nb082_alpha_dummy_003 A B R),
        (nb082_alpha_dummy_004 A B R p))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb082_split_alpha_0001 A B R p)))))))))

theorem nb082_focused_notmem_0000 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_001 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪
          ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0106 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_001 A B R) ∉ ((syn_cxpk B B)).fv := by
  simpa only [nb082_alpha_dummy_001, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0000 A B R) (nb082_focused_notmem_0000 A B R))

theorem nb082_focused_notmem_0001 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_002 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0107 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_002 A B R p) ∉ ((syn_cxpk B B)).fv := by
  simpa only [nb082_alpha_dummy_002, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0001 A B R p) (nb082_focused_notmem_0001 A B R p))

theorem nb082_focused_notmem_0002 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_000 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb082_wpp_notmem_0108 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_000 A B R) ∉ ((syn_cxpk B B)).fv := by
  simpa only [nb082_alpha_dummy_000, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0002 A B R) (nb082_focused_notmem_0002 A B R))

theorem nb082_wpp_notmem_0109 (B : Class) (p : Var) (dv_B_p : p ∉ B.fv) :
    p ∉ ((syn_cxpk B B)).fv := by
  simpa only [fv_syn_cxpk, Finset.mem_union, not_or] using (And.intro dv_B_p dv_B_p)

theorem nb082_focused_notmem_0003 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_003 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪
            ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R))
                (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R))
        (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0110 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_003 A B R) ∉ ((syn_cxpk B B)).fv := by
  simpa only [nb082_alpha_dummy_003, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0003 A B R) (nb082_focused_notmem_0003 A B R))

theorem nb082_focused_notmem_0004 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_004 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
                (syn_cfdminvalp R A B (Class.cv p))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
        (syn_cfdminvalp R A B (Class.cv p)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv p) (syn_cxpk B B)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0111 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_004 A B R p) ∉ ((syn_cxpk B B)).fv := by
  simpa only [nb082_alpha_dummy_004, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0004 A B R p) (nb082_focused_notmem_0004 A B R p))

theorem nb082_compact_envfresh_0007 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_B_p : p ∉ B.fv) :
    TEnvFresh
      [((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      ((syn_cxpk B B)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R) (nb082_alpha_dummy_002 A B R p)
      (nb082_wpp_notmem_0106 A B R) (nb082_wpp_notmem_0107 A B R p)
      (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p (nb082_wpp_notmem_0108 A B R)
        (nb082_wpp_notmem_0109 B p dv_B_p)
        (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R) (nb082_alpha_dummy_004 A B R p)
          (nb082_wpp_notmem_0110 A B R) (nb082_wpp_notmem_0111 A B R p)
          (TEnvFresh.nil ((syn_cxpk B B)).fv))))

@[expose]
noncomputable def nb082_wpp_refl_0007 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_B_p : p ∉ B.fv) :
    TReflOn
      [((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      ((syn_cxpk B B)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0007 A B R p dv_B_p)

theorem nb082_focused_notmem_0005 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_050 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪
          ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0006 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_050 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪
          ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0007 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_050 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪
          ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0112 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_050 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_050, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0005 A B R) (nb082_focused_notmem_0006 A B R))
      (nb082_focused_notmem_0007 A B R))

theorem nb082_focused_notmem_0008 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_052 A B R p) ∉ A.fv :=
  by
  change
    freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0009 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_052 A B R p) ∉ B.fv :=
  by
  change
    freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0010 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_052 A B R p) ∉ R.fv :=
  by
  change
    freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0113 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_052 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_052, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0008 A B R p) (nb082_focused_notmem_0009 A B R p))
      (nb082_focused_notmem_0010 A B R p))

theorem nb082_focused_notmem_0011 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_049 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪
          ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0012 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_049 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪
          ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0013 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_049 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪
          ((syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0114 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_049 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_049, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0011 A B R) (nb082_focused_notmem_0012 A B R))
      (nb082_focused_notmem_0013 A B R))

theorem nb082_focused_notmem_0014 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_051 A B R p) ∉ A.fv :=
  by
  change
    freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0015 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_051 A B R p) ∉ B.fv :=
  by
  change
    freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0016 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_051 A B R p) ∉ R.fv :=
  by
  change
    freshVar (((syn_ccnvk (syn_cfdminsep R A B))).fv ∪ ((syn_csn (Class.cv p))).fv) 0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0115 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_051 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_051, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0014 A B R p) (nb082_focused_notmem_0015 A B R p))
      (nb082_focused_notmem_0016 A B R p))

theorem nb082_focused_notmem_0017 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_047 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0018 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_047 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0019 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_047 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))).fv ∪ ((syn_c1c)).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0116 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_047 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_047, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0017 A B R) (nb082_focused_notmem_0018 A B R))
      (nb082_focused_notmem_0019 A B R))

theorem nb082_focused_notmem_0020 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_048 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪
          ((syn_c1c)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0021 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_048 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪
          ((syn_c1c)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0022 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_048 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))).fv ∪
          ((syn_c1c)).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0117 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_048 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_048, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0020 A B R p) (nb082_focused_notmem_0021 A B R p))
      (nb082_focused_notmem_0022 A B R p))

theorem nb082_focused_notmem_0023 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_045 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin
              (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0024 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_045 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin
              (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0025 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_045 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv ∪ ((syn_cnin
              (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
                (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0118 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_045 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_045, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0023 A B R) (nb082_focused_notmem_0024 A B R))
      (nb082_focused_notmem_0025 A B R))

theorem nb082_focused_notmem_0026 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_046 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))).fv ∪
          ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0027 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_046 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))).fv ∪
          ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0028 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_046 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))).fv ∪
          ((syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
              (syn_c1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0119 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_046 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_046, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0026 A B R p) (nb082_focused_notmem_0027 A B R p))
      (nb082_focused_notmem_0028 A B R p))

theorem nb082_focused_notmem_0029 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_042 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0030 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_042 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0031 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_042 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0120 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_042 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_042, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0029 A B R) (nb082_focused_notmem_0030 A B R))
      (nb082_focused_notmem_0031 A B R))

theorem nb082_focused_notmem_0032 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_044 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))).fv)
        1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0033 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_044 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))).fv)
        1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0034 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_044 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0121 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_044 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_044, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0032 A B R p) (nb082_focused_notmem_0033 A B R p))
      (nb082_focused_notmem_0034 A B R p))

theorem nb082_focused_notmem_0035 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_041 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0036 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_041 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0037 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_041 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
              (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))) (syn_c1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
        (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R))))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B))
      (syn_csn (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0122 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_041 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_041, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0035 A B R) (nb082_focused_notmem_0036 A B R))
      (nb082_focused_notmem_0037 A B R))

theorem nb082_focused_notmem_0038 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_043 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
