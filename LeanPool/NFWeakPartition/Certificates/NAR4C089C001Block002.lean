/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C089C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C089C001Part004`. -/


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
noncomputable def nb089_split_alpha_0000 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_008 A B R))
          (Class.cv (nb089_alpha_dummy_003 A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
            (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_010 u A B R))
          (Class.cv (nb089_alpha_dummy_004 u A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
            (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_008 A B R) from (by
              unfold nb089_alpha_dummy_008;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))))
          (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_010 u A B R) from (by
              unfold nb089_alpha_dummy_010;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))))
          (TAlphaVar.there
            (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_007 A B R) from (by
                unfold nb089_alpha_dummy_007;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))))
            (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_009 u A B R) from (by
                unfold nb089_alpha_dummy_009;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))))
            (TAlphaVar.there
              (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_037 A B R) from (by
                  unfold nb089_alpha_dummy_037;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0038 A B R) 0))))
              (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_038 u A B R) from (by
                  unfold nb089_alpha_dummy_038;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb089_support_mem_0039 u A B R) 0)))) (TAlphaVar.there
                (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_011 A B R) from (by
                    unfold nb089_alpha_dummy_011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0035 A B R) 0))))
                (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_012 u A B R) from (by
                    unfold nb089_alpha_dummy_012;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0037 u A B R) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
                ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (by decide)) (freshVar_injective
              (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_008 A B R) ≠
                                        (nb089_alpha_dummy_015 A B R) from (by
                                        unfold nb089_alpha_dummy_015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 0)))) (show
                                      (nb089_alpha_dummy_010 u A B R) ≠
                                        (nb089_alpha_dummy_017 u A B R) from (by
                                        unfold nb089_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089_alpha_dummy_008 A B R) ≠
        (nb089_alpha_dummy_016 A B R) from (by
                                          unfold nb089_alpha_dummy_016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0012 A B R) 1)))) (show
                                        (nb089_alpha_dummy_010 u A B R) ≠
        (nb089_alpha_dummy_018 u A B R) from (by
                                          unfold nb089_alpha_dummy_018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0013 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089_alpha_dummy_008 A B R) ≠
        (nb089_alpha_dummy_041 A B R) from (by
          unfold nb089_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0042 A B R) 0)))) (show (nb089_alpha_dummy_010 u A B R) ≠
        (nb089_alpha_dummy_042 u A B R) from (by
          unfold nb089_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0043 u A B R) 0)))) (TAlphaVar.there (show
        (nb089_alpha_dummy_008 A B R) ≠ (nb089_alpha_dummy_039 A B R) from (by
          unfold nb089_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0040 A B R) 0)))) (show (nb089_alpha_dummy_010 u A B R) ≠
        (nb089_alpha_dummy_040 u A B R) from (by
          unfold nb089_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0041 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_008 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_022 A B R)
        from (by
          unfold nb089_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  1)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_025 u A B R)
        from (by
          unfold nb089_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_021 A B R) from (by
          unfold nb089_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_024 u A B R)
        from (by
          unfold nb089_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold
            nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_029 A B R)
        from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_033 A B R)
        from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022
        A B R) ≠ (nb089_alpha_dummy_033 A B R) from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠ (nb089_alpha_dummy_035 A B R)
        from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_035 A B R) from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_019 A B R)
        from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_008 A B R) ≠
                                        (nb089_alpha_dummy_015 A B R) from (by
                                        unfold nb089_alpha_dummy_015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 0)))) (show
                                      (nb089_alpha_dummy_010 u A B R) ≠
                                        (nb089_alpha_dummy_017 u A B R) from (by
                                        unfold nb089_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089_alpha_dummy_008 A B R) ≠
        (nb089_alpha_dummy_016 A B R) from (by
                                          unfold nb089_alpha_dummy_016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0012 A B R) 1)))) (show
                                        (nb089_alpha_dummy_010 u A B R) ≠
        (nb089_alpha_dummy_018 u A B R) from (by
                                          unfold nb089_alpha_dummy_018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0013 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089_alpha_dummy_008 A B R) ≠
        (nb089_alpha_dummy_041 A B R) from (by
          unfold nb089_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0042 A B R) 0)))) (show (nb089_alpha_dummy_010 u A B R) ≠
        (nb089_alpha_dummy_042 u A B R) from (by
          unfold nb089_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0043 u A B R) 0)))) (TAlphaVar.there (show
        (nb089_alpha_dummy_008 A B R) ≠ (nb089_alpha_dummy_039 A B R) from (by
          unfold nb089_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0040 A B R) 0)))) (show (nb089_alpha_dummy_010 u A B R) ≠
        (nb089_alpha_dummy_040 u A B R) from (by
          unfold nb089_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0041 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_008 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_022 A B R)
        from (by
          unfold nb089_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  1)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_025 u A B R)
        from (by
          unfold nb089_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_021 A B R) from (by
          unfold nb089_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_024 u A B R)
        from (by
          unfold nb089_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold
            nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_029 A B R)
        from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_033 A B R)
        from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022
        A B R) ≠ (nb089_alpha_dummy_033 A B R) from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠ (nb089_alpha_dummy_035 A B R)
        from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_035 A B R) from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_019 A B R)
        from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_041 A B R), (nb089_alpha_dummy_042 u A B R)),
        ((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb089_alpha_dummy_039 A B R), (nb089_alpha_dummy_040 u A B R)),
                    ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
                    ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
                    ((nb089_alpha_dummy_037 A B R), (nb089_alpha_dummy_038 u A B R)),
                    ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
                    ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
                    ((nb089_alpha_dummy_000 A B R), u),
                    ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
                    ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part005`. -/


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
noncomputable def nb089_split_alpha_0001 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_011 A B R)) (syn_ccompl
            (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
                (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089_alpha_dummy_011 A B R)) (syn_ccompl
              (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
                  (Class.cv (nb089_alpha_dummy_003 A B R))
                  (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                    (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_012 u A B R)) (syn_ccompl
            (Class.cab (nb089_alpha_dummy_009 u A B R)
              (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089_alpha_dummy_012 u A B R)) (syn_ccompl
              (Class.cab (nb089_alpha_dummy_009 u A B R)
                (syn_wrex (nb089_alpha_dummy_010 u A B R)
                  (Class.cv (nb089_alpha_dummy_004 u A B R))
                  (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                    (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_008 A B R) from
                            (by
                              unfold nb089_alpha_dummy_008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
                          (show u ≠ (nb089_alpha_dummy_010 u A B R) from (by
                              unfold nb089_alpha_dummy_010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                      1)))) (TAlphaVar.there (show
                              (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_007 A B R) from
                              (by
                                unfold nb089_alpha_dummy_007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0006 A B R)
                                        0)))) (show u ≠ (nb089_alpha_dummy_009 u A B R) from (by
                                unfold nb089_alpha_dummy_009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_013 A B R)
                                from (by
                                  unfold nb089_alpha_dummy_013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0010 A B R)
                                          0)))) (show u ≠ (nb089_alpha_dummy_014 u A B R) from
                                (by
                                  unfold nb089_alpha_dummy_014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0011 u A B R)
                                          0)))) (TAlphaVar.there (show
                                  (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_011 A B R)
                                  from (by
                                    unfold nb089_alpha_dummy_011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb089_support_mem_0007 A B R)
                                            0)))) (show u ≠ (nb089_alpha_dummy_012 u A B R) from
                                  (by
                                    unfold nb089_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb089_support_mem_0009 u A B R) 0))))
                                (TAlphaVar.there (show (nb089_alpha_dummy_000 A B R) ≠
                                      (nb089_alpha_dummy_003 A B R) from (by
                                      unfold nb089_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0004 A B R) 0))))
                                  (show u ≠ (nb089_alpha_dummy_004 u A B R) from (by
                                      unfold nb089_alpha_dummy_004;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0005 u A B R) 0))))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
                              ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (by decide))
                          (freshVar_injective (((Class.cv u)).fv ∪
                              ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb089_alpha_dummy_008 A B R) ≠
                                      (nb089_alpha_dummy_015 A B R) from (by
                                      unfold nb089_alpha_dummy_015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0012 A B R) 0)))) (show
                                    (nb089_alpha_dummy_010 u A B R) ≠
                                      (nb089_alpha_dummy_017 u A B R) from (by
                                      unfold nb089_alpha_dummy_017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0013 u A B R) 0))))
                                  (TAlphaVar.there (show (nb089_alpha_dummy_008 A B R) ≠
                                        (nb089_alpha_dummy_016 A B R) from (by
                                        unfold nb089_alpha_dummy_016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 1)))) (show
                                      (nb089_alpha_dummy_010 u A B R) ≠
                                        (nb089_alpha_dummy_018 u A B R) from (by
                                        unfold nb089_alpha_dummy_018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_022 A B R) from (by
          unfold nb089_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016 A
                    B R)
                  1)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_025 u A B R)
        from (by
          unfold nb089_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017 u
                    A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_021 A B R) from (by
          unfold nb089_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_024 u A B R)
        from (by
          unfold nb089_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_029 A B R)
        from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_033 A B R)
        from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022
        A B R) ≠ (nb089_alpha_dummy_033 A B R) from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠ (nb089_alpha_dummy_035 A B R)
        from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_035 A B R) from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R) 0)))) (show (nb089_alpha_dummy_017 u A B R) ≠
        (nb089_alpha_dummy_020 u A B R) from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_008 A B R) from
                            (by
                              unfold nb089_alpha_dummy_008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
                          (show u ≠ (nb089_alpha_dummy_010 u A B R) from (by
                              unfold nb089_alpha_dummy_010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                      1)))) (TAlphaVar.there (show
                              (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_007 A B R) from
                              (by
                                unfold nb089_alpha_dummy_007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0006 A B R)
                                        0)))) (show u ≠ (nb089_alpha_dummy_009 u A B R) from (by
                                unfold nb089_alpha_dummy_009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_013 A B R)
                                from (by
                                  unfold nb089_alpha_dummy_013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0010 A B R)
                                          0)))) (show u ≠ (nb089_alpha_dummy_014 u A B R) from
                                (by
                                  unfold nb089_alpha_dummy_014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0011 u A B R)
                                          0)))) (TAlphaVar.there (show
                                  (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_011 A B R)
                                  from (by
                                    unfold nb089_alpha_dummy_011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb089_support_mem_0007 A B R)
                                            0)))) (show u ≠ (nb089_alpha_dummy_012 u A B R) from
                                  (by
                                    unfold nb089_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb089_support_mem_0009 u A B R) 0))))
                                (TAlphaVar.there (show (nb089_alpha_dummy_000 A B R) ≠
                                      (nb089_alpha_dummy_003 A B R) from (by
                                      unfold nb089_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0004 A B R) 0))))
                                  (show u ≠ (nb089_alpha_dummy_004 u A B R) from (by
                                      unfold nb089_alpha_dummy_004;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0005 u A B R) 0))))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
                              ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (by decide))
                          (freshVar_injective (((Class.cv u)).fv ∪
                              ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb089_alpha_dummy_008 A B R) ≠
                                      (nb089_alpha_dummy_015 A B R) from (by
                                      unfold nb089_alpha_dummy_015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0012 A B R) 0)))) (show
                                    (nb089_alpha_dummy_010 u A B R) ≠
                                      (nb089_alpha_dummy_017 u A B R) from (by
                                      unfold nb089_alpha_dummy_017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0013 u A B R) 0))))
                                  (TAlphaVar.there (show (nb089_alpha_dummy_008 A B R) ≠
                                        (nb089_alpha_dummy_016 A B R) from (by
                                        unfold nb089_alpha_dummy_016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 1)))) (show
                                      (nb089_alpha_dummy_010 u A B R) ≠
                                        (nb089_alpha_dummy_018 u A B R) from (by
                                        unfold nb089_alpha_dummy_018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_022 A B R) from (by
          unfold nb089_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016 A
                    B R)
                  1)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_025 u A B R)
        from (by
          unfold nb089_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017 u
                    A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_021 A B R) from (by
          unfold nb089_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_024 u A B R)
        from (by
          unfold nb089_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_029 A B R)
        from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_029 A B R) from (by
          unfold
            nb089_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_030 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_027 A B R) from (by
          unfold
            nb089_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_028 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_023 A B R), (nb089_alpha_dummy_026 u A B R)),
        ((nb089_alpha_dummy_022 A B R), (nb089_alpha_dummy_025 u A B R)),
        ((nb089_alpha_dummy_021 A B R), (nb089_alpha_dummy_024 u A B R)),
        ((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_033 A B R)
        from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_022
        A B R) ≠ (nb089_alpha_dummy_033 A B R) from (by
          unfold
            nb089_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_034 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_022 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_015
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠ (nb089_alpha_dummy_035 A B R)
        from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_023
        A B R) ≠ (nb089_alpha_dummy_035 A B R) from (by
          unfold
            nb089_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_036 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_023 A B R) ≠
        (nb089_alpha_dummy_031 A B R) from (by
          unfold
            nb089_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_026 u A B R) ≠ (nb089_alpha_dummy_032 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb089_alpha_dummy_015 A B R) ≠
        (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R) 0)))) (show (nb089_alpha_dummy_017 u A B R) ≠
        (nb089_alpha_dummy_020 u A B R) from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_019 A B R) from (by
          unfold nb089_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_020 u A B R)
        from (by
          unfold nb089_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_019 A B R), (nb089_alpha_dummy_020 u A B R)),
        ((nb089_alpha_dummy_015 A B R), (nb089_alpha_dummy_017 u A B R)),
        ((nb089_alpha_dummy_016 A B R), (nb089_alpha_dummy_018 u A B R)),
        ((nb089_alpha_dummy_008 A B R), (nb089_alpha_dummy_010 u A B R)),
        ((nb089_alpha_dummy_007 A B R), (nb089_alpha_dummy_009 u A B R)),
        ((nb089_alpha_dummy_013 A B R), (nb089_alpha_dummy_014 u A B R)),
        ((nb089_alpha_dummy_011 A B R), (nb089_alpha_dummy_012 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb089_split_alpha_0000 u A B R)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb089_split_alpha_0000 u A B R)))))))))))

theorem nb089_focused_notmem_0000 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
            ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 (syn_cuni A))]
  rw [fv_syn_cpw1 (syn_cuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0114 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_003, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0000 A B R)

theorem nb089_focused_notmem_0001 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 (syn_cuni A))]
  rw [fv_syn_cpw1 (syn_cuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0115 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_004, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0001 u A B R)

theorem nb089_focused_notmem_0002 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_wpp_notmem_0116 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_000, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0002 A B R)

theorem nb089_wpp_notmem_0117 (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    u ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [fv_syn_cpw1, fv_syn_cuni] using dv_A_u

theorem nb089_focused_notmem_0003 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_005 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
            ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
                (syn_cpw1 (syn_cpw1 (syn_cuni A))))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
                (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
        (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb089_alpha_dummy_000 A B R))
      (syn_cpw1 (syn_cpw1 (syn_cuni A)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 (syn_cuni A))]
  rw [fv_syn_cpw1 (syn_cuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0118 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_005 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_005, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0003 A B R)

theorem nb089_focused_notmem_0004 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_006 u A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 (syn_cuni A))]
  rw [fv_syn_cpw1 (syn_cuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0119 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_006 u A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_006, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0004 u A B R)

theorem nb089_focused_notmem_0005 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_wbr R (syn_cwe) A)).fv ∪
            ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪
          ((syn_c0)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [fv_syn_wbr R (syn_cwe) A]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0120 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_001, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0005 A B R)

theorem nb089_focused_notmem_0006 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [fv_syn_wbr R (syn_cwe) A]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0121 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
  simpa only [nb089_alpha_dummy_002, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0006 u A B R)

theorem nb089_compact_envfresh_0007 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) :
    TEnvFresh
      [((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R)
      (nb089_wpp_notmem_0114 A B R) (nb089_wpp_notmem_0115 u A B R)
      (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0116 A B R)
        (nb089_wpp_notmem_0117 u A dv_A_u)
        (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R) (nb089_alpha_dummy_006 u A B R)
          (nb089_wpp_notmem_0118 A B R) (nb089_wpp_notmem_0119 u A B R)
          (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R)
            (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0120 A B R)
            (nb089_wpp_notmem_0121 u A B R)
            (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv)))))

@[expose]
noncomputable def nb089_wpp_refl_0007 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) :
    TReflOn
      [((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0007 u A B R dv_A_u)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
