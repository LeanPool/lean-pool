/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part002

/-! NF weak partition development: NAR4H5C093M3Part003. -/


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
noncomputable def nb093_split_alpha_0002 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_070 A))
          (Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_070 A))
            (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_071 r))
          (Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_071 r))
            (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_065 A) from (by
                      unfold nb093_alpha_dummy_065;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
                  (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_067 r) from (by
                      unfold nb093_alpha_dummy_067;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))))
                  (TAlphaVar.there
                    (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_064 A) from (by
                        unfold nb093_alpha_dummy_064;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
                    (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_066 r) from (by
                        unfold nb093_alpha_dummy_066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0058 r) 0)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_070 A) from (by
                          unfold nb093_alpha_dummy_070;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0060 A) 0))))
                      (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_071 r) from (by
                          unfold nb093_alpha_dummy_071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0061 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_068 A) from (by
                            unfold nb093_alpha_dummy_068;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0057 A) 0))))
                        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_069 r) from (by
                            unfold nb093_alpha_dummy_069;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0059 r) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
                      ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪
                      ((Class.cv (nb093_alpha_dummy_061 r))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_072 A) from (by
                              unfold nb093_alpha_dummy_072;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                          (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_074 r) from (by
                              unfold nb093_alpha_dummy_074;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0063 r) 0))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_073 A) from (by
                                unfold nb093_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                            (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_075 r) from (by
                                unfold nb093_alpha_dummy_075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0063 r) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_079 A) from (by
          unfold nb093_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 1)))) (show (nb093_alpha_dummy_074 r) ≠
        (nb093_alpha_dummy_082 r) from (by
          unfold nb093_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_078 A) from (by
          unfold nb093_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 0)))) (show (nb093_alpha_dummy_074 r) ≠
        (nb093_alpha_dummy_081 r) from (by
          unfold nb093_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from (by
          unfold nb093_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A)
                  0)))) (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from (by
          unfold nb093_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A),
        (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)),
        ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A),
        (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A),
        (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A),
        (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)),
        ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A),
        (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A),
        (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074
        r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_080
        A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_080
        A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from
                                      (by
                                        unfold nb093_alpha_dummy_076;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0064 A)
                                                0)))) (show (nb093_alpha_dummy_074 r) ≠
                                        (nb093_alpha_dummy_077 r) from (by
                                        unfold nb093_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0065 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                                    ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                                    ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                                    ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                                    ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                                    ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
                                    ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                                    ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                    ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                    ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                    ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                    ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                    ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                    ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                    ((nb093_alpha_dummy_000 A), d),
                                    ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
                                      (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
                                      (nb093_alpha_dummy_005 A r d)),
                                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from
                                    (by
                                      unfold nb093_alpha_dummy_076;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0064 A)
                                              0)))) (show
                                    (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from
                                    (by
                                      unfold nb093_alpha_dummy_077;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0065 r)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from
                                      (by
                                        unfold nb093_alpha_dummy_076;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0064 A)
                                                0)))) (show (nb093_alpha_dummy_074 r) ≠
                                        (nb093_alpha_dummy_077 r) from (by
                                        unfold nb093_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0065 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                                    ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                                    ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                                    ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                                    ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                                    ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
                                    ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                                    ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                    ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                    ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                    ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                    ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                    ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                    ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                    ((nb093_alpha_dummy_000 A), d),
                                    ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
                                      (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
                                      (nb093_alpha_dummy_005 A r d)),
                                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_065 A) from (by
                        unfold nb093_alpha_dummy_065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
                    (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_067 r) from (by
                        unfold nb093_alpha_dummy_067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0058 r) 1)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_064 A) from (by
                          unfold nb093_alpha_dummy_064;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
                      (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_066 r) from (by
                          unfold nb093_alpha_dummy_066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0058 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_070 A) from (by
                            unfold nb093_alpha_dummy_070;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0060 A) 0))))
                        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_071 r) from (by
                            unfold nb093_alpha_dummy_071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0061 r) 0))))
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_068 A) from (by
                              unfold nb093_alpha_dummy_068;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0057 A) 0))))
                          (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_069 r) from (by
                              unfold nb093_alpha_dummy_069;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0059 r) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_001 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv r)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
                        ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪
                        ((Class.cv (nb093_alpha_dummy_061 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_072 A) from (by
                                unfold nb093_alpha_dummy_072;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                            (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_074 r) from (by
                                unfold nb093_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0063 r) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_073 A) from
                                (by
                                  unfold nb093_alpha_dummy_073;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                              (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_075 r) from
                                (by
                                  unfold nb093_alpha_dummy_075;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0063 r) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_065 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_067 r))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_079 A) from (by
          unfold nb093_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 1)))) (show (nb093_alpha_dummy_074 r) ≠
        (nb093_alpha_dummy_082 r) from (by
          unfold nb093_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_078 A) from (by
          unfold nb093_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A)
                  0)))) (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_081 r) from (by
          unfold nb093_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_072 A) ≠
        (nb093_alpha_dummy_076 A) from (by
          unfold nb093_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A)
                  0)))) (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from (by
          unfold nb093_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A),
        (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)),
        ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A),
        (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A),
        (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A),
        (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)),
        ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A),
        (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A),
        (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_079
        A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_080
        A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_080
        A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A)
                                        from (by
                                          unfold nb093_alpha_dummy_076;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0064 A) 0)))) (show
                                        (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r)
                                        from (by
                                          unfold nb093_alpha_dummy_077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0065 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                                      ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                                      ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                                      ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                                      ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                                      ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
                                      ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                                      ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                      ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                      ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                      ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                      ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                      ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                      ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                      ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                      ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                      ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                      ((nb093_alpha_dummy_000 A), d),
                                      ((nb093_alpha_dummy_001 A), r),
                                      ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                                      ((nb093_alpha_dummy_004 A),
                                        (nb093_alpha_dummy_005 A r d)),
                                      ((nb093_alpha_dummy_002 A),
                                        (nb093_alpha_dummy_003 A r d))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from
                                      (by
                                        unfold nb093_alpha_dummy_076;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0064 A)
                                                0)))) (show (nb093_alpha_dummy_074 r) ≠
                                        (nb093_alpha_dummy_077 r) from (by
                                        unfold nb093_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0065 r)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A)
                                        from (by
                                          unfold nb093_alpha_dummy_076;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0064 A) 0)))) (show
                                        (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r)
                                        from (by
                                          unfold nb093_alpha_dummy_077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0065 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                                      ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                                      ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                                      ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                                      ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                                      ((nb093_alpha_dummy_070 A), (nb093_alpha_dummy_071 r)),
                                      ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                                      ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                      ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                      ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                      ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                      ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                      ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                      ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                      ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                      ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                      ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                      ((nb093_alpha_dummy_000 A), d),
                                      ((nb093_alpha_dummy_001 A), r),
                                      ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                                      ((nb093_alpha_dummy_004 A),
                                        (nb093_alpha_dummy_005 A r d)),
                                      ((nb093_alpha_dummy_002 A),
                                        (nb093_alpha_dummy_003 A r d))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb093_split_alpha_0003 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
        ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
        ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_098 A))
          (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_098 A))
            (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_099 r))
          (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_099 r))
            (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_072 A) from (by
                      unfold nb093_alpha_dummy_072;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                  (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_074 r) from (by
                      unfold nb093_alpha_dummy_074;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 0))))
                  (TAlphaVar.there
                    (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_073 A) from (by
                        unfold nb093_alpha_dummy_073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                    (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_075 r) from (by
                        unfold nb093_alpha_dummy_075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0063 r) 1)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_098 A) from (by
                          unfold nb093_alpha_dummy_098;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0092 A) 0))))
                      (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_099 r) from (by
                          unfold nb093_alpha_dummy_099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0093 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_096 A) from (by
                            unfold nb093_alpha_dummy_096;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0090 A) 0))))
                        (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_097 r) from (by
                            unfold nb093_alpha_dummy_097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0091 r) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_079 A) from
                                      (by
                                        unfold nb093_alpha_dummy_079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0066 A)
                                                1)))) (show (nb093_alpha_dummy_074 r) ≠
                                        (nb093_alpha_dummy_082 r) from (by
                                        unfold nb093_alpha_dummy_082;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0067 r)
                                                1)))) (TAlphaVar.there (show
                                        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_078 A)
                                        from (by
                                          unfold nb093_alpha_dummy_078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0066 A) 0)))) (show
                                        (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_081 r)
                                        from (by
                                          unfold nb093_alpha_dummy_081;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0067 r) 0))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_072 A) ≠
        (nb093_alpha_dummy_076 A) from (by
          unfold nb093_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A) 0)))) (show (nb093_alpha_dummy_074 r) ≠
        (nb093_alpha_dummy_077 r) from (by
          unfold nb093_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_080 A),
        (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)),
                                        ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)),
                                        ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                                        ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                                        ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                                        ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
                                        ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
                                        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                                        ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                                        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
                                        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                                        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                        ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                        ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                        ((nb093_alpha_dummy_000 A), d),
                                        ((nb093_alpha_dummy_001 A), r),
                                        ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)),
        ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A),
        (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
        ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A),
        (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
        ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A),
        (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A),
        (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from (by
                                unfold nb093_alpha_dummy_076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                            (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from (by
                                unfold nb093_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                            ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                            ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                            ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
                            ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
                            ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                            ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                            ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
                            ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                            ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                            ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                            ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                            ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                            ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                            ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                            ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                            ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                            ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                            ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                            ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                            ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                            ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                            ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from (by
                              unfold nb093_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                          (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from (by
                              unfold nb093_alpha_dummy_077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from (by
                                unfold nb093_alpha_dummy_076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                            (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from (by
                                unfold nb093_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                            ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                            ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                            ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
                            ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
                            ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                            ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                            ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
                            ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                            ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                            ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                            ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                            ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                            ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                            ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                            ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                            ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                            ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                            ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                            ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                            ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                            ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                            ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_072 A) from (by
                        unfold nb093_alpha_dummy_072;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                    (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_074 r) from (by
                        unfold nb093_alpha_dummy_074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0063 r) 0)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_073 A) from (by
                          unfold nb093_alpha_dummy_073;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                      (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_075 r) from (by
                          unfold nb093_alpha_dummy_075;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0063 r) 1))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_098 A) from (by
                            unfold nb093_alpha_dummy_098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0092 A) 0))))
                        (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_099 r) from (by
                            unfold nb093_alpha_dummy_099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0093 r) 0))))
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_065 A) ≠ (nb093_alpha_dummy_096 A) from (by
                              unfold nb093_alpha_dummy_096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0090 A) 0))))
                          (show (nb093_alpha_dummy_067 r) ≠ (nb093_alpha_dummy_097 r) from (by
                              unfold nb093_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0091 r) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb093_alpha_dummy_065 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093_alpha_dummy_067 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb093_alpha_dummy_072 A) ≠
        (nb093_alpha_dummy_079 A) from (by
                                          unfold nb093_alpha_dummy_079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0066 A) 1)))) (show
                                        (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_082 r)
                                        from (by
                                          unfold nb093_alpha_dummy_082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0067 r) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_072 A) ≠
        (nb093_alpha_dummy_078 A) from (by
          unfold nb093_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 0)))) (show (nb093_alpha_dummy_074 r) ≠
        (nb093_alpha_dummy_081 r) from (by
          unfold nb093_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from (by
          unfold nb093_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A) 0)))) (show (nb093_alpha_dummy_074 r) ≠
        (nb093_alpha_dummy_077 r) from (by
          unfold nb093_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_080 A),
        (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A), (nb093_alpha_dummy_082 r)),
        ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)), ((nb093_alpha_dummy_076 A),
        (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
        ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)), ((nb093_alpha_dummy_098 A),
        (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
        ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A),
        (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
        ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_086 A) from (by
          unfold
            nb093_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_087 r) from (by
          unfold
            nb093_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_084 A) from (by
          unfold
            nb093_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_085 r) from (by
          unfold
            nb093_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_080 A), (nb093_alpha_dummy_083 r)), ((nb093_alpha_dummy_079 A),
        (nb093_alpha_dummy_082 r)), ((nb093_alpha_dummy_078 A), (nb093_alpha_dummy_081 r)),
        ((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)), ((nb093_alpha_dummy_072 A),
        (nb093_alpha_dummy_074 r)), ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
        ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)), ((nb093_alpha_dummy_096 A),
        (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
        ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)), ((nb093_alpha_dummy_094 A),
        (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A),
        (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A),
        (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A),
        (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠ (nb093_alpha_dummy_090 A) from (by
          unfold
            nb093_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_091 r) from (by
          unfold
            nb093_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_079 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093_alpha_dummy_082 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_072
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_080 A) ≠ (nb093_alpha_dummy_092 A) from (by
          unfold
            nb093_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_093 r) from (by
          unfold
            nb093_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_080 A) ≠
        (nb093_alpha_dummy_088 A) from (by
          unfold
            nb093_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093_alpha_dummy_083 r) ≠ (nb093_alpha_dummy_089 r) from (by
          unfold
            nb093_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from
                                (by
                                  unfold nb093_alpha_dummy_076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                              (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from
                                (by
                                  unfold nb093_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                              ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                              ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                              ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
                              ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
                              ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                              ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                              ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
                              ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                              ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                              ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                              ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                              ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                              ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                              ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                              ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                              ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                              ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                              ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                              ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                              ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                              ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                              ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from (by
                                unfold nb093_alpha_dummy_076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                            (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from (by
                                unfold nb093_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093_alpha_dummy_072 A) ≠ (nb093_alpha_dummy_076 A) from
                                (by
                                  unfold nb093_alpha_dummy_076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                              (show (nb093_alpha_dummy_074 r) ≠ (nb093_alpha_dummy_077 r) from
                                (by
                                  unfold nb093_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb093_alpha_dummy_076 A), (nb093_alpha_dummy_077 r)),
                              ((nb093_alpha_dummy_072 A), (nb093_alpha_dummy_074 r)),
                              ((nb093_alpha_dummy_073 A), (nb093_alpha_dummy_075 r)),
                              ((nb093_alpha_dummy_098 A), (nb093_alpha_dummy_099 r)),
                              ((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)),
                              ((nb093_alpha_dummy_065 A), (nb093_alpha_dummy_067 r)),
                              ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
                              ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)),
                              ((nb093_alpha_dummy_068 A), (nb093_alpha_dummy_069 r)),
                              ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                              ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                              ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                              ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                              ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                              ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                              ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                              ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                              ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                              ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                              ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                              ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                              ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                              ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
