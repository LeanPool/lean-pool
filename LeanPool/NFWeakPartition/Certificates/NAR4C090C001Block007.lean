/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C090C001Part025Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part025`. -/


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
noncomputable def nb090_split_alpha_0001 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
        ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_063 A))
          (Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_063 A))
            (Class.cab (nb090_alpha_dummy_057 A)
              (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_064 h))
          (Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_064 h))
            (Class.cab (nb090_alpha_dummy_059 h)
              (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_058 A) from (by
                      unfold nb090_alpha_dummy_058;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
                  (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_060 h) from (by
                      unfold nb090_alpha_dummy_060;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_057 A) from (by
                        unfold nb090_alpha_dummy_057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
                    (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_059 h) from (by
                        unfold nb090_alpha_dummy_059;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0048 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_063 A) from (by
                          unfold nb090_alpha_dummy_063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0050 A) 0))))
                      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_064 h) from (by
                          unfold nb090_alpha_dummy_064;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0051 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_061 A) from (by
                            unfold nb090_alpha_dummy_061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0047 A) 0))))
                        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_062 h) from (by
                            unfold nb090_alpha_dummy_062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0049 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
                              ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_050 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_065 A) from (by
                              unfold nb090_alpha_dummy_065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                          (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_067 h) from (by
                              unfold nb090_alpha_dummy_067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_066 A) from (by
                                unfold nb090_alpha_dummy_066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                            (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_068 h) from (by
                                unfold nb090_alpha_dummy_068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_072 A) from (by
          unfold nb090_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_075 h) from (by
          unfold nb090_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_071 A) from (by
          unfold nb090_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 0)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_074 h) from (by
          unfold nb090_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from (by
          unfold nb090_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A)
                  0)))) (show (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from (by
          unfold nb090_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A),
        (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
        ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_072
        A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A),
        (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
        ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                      (by
                                        unfold nb090_alpha_dummy_069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0054 A)
                                                0)))) (show (nb090_alpha_dummy_067 h) ≠
                                        (nb090_alpha_dummy_070 h) from (by
                                        unfold nb090_alpha_dummy_070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0055 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                    ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                    ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                    ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                    ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                    ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
                                    ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                    ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                    (by
                                      unfold nb090_alpha_dummy_069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from
                                    (by
                                      unfold nb090_alpha_dummy_070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                      (by
                                        unfold nb090_alpha_dummy_069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0054 A)
                                                0)))) (show (nb090_alpha_dummy_067 h) ≠
                                        (nb090_alpha_dummy_070 h) from (by
                                        unfold nb090_alpha_dummy_070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0055 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                    ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                    ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                    ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                    ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                    ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
                                    ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                    ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_058 A) from (by
                        unfold nb090_alpha_dummy_058;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
                    (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_060 h) from (by
                        unfold nb090_alpha_dummy_060;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0048 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_057 A) from (by
                          unfold nb090_alpha_dummy_057;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
                      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_059 h) from (by
                          unfold nb090_alpha_dummy_059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0048 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_063 A) from (by
                            unfold nb090_alpha_dummy_063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0050 A) 0))))
                        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_064 h) from (by
                            unfold nb090_alpha_dummy_064;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0051 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_061 A) from (by
                              unfold nb090_alpha_dummy_061;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0047 A) 0))))
                          (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_062 h) from (by
                              unfold nb090_alpha_dummy_062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0049 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
                                ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_050 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_065 A) from (by
                                unfold nb090_alpha_dummy_065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                            (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_067 h) from (by
                                unfold nb090_alpha_dummy_067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_066 A) from
                                (by
                                  unfold nb090_alpha_dummy_066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                              (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_068 h) from
                                (by
                                  unfold nb090_alpha_dummy_068;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_058 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_060 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_072 A) from (by
          unfold nb090_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_075 h) from (by
          unfold nb090_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_071 A) from (by
          unfold nb090_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A)
                  0)))) (show (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_074 h) from (by
          unfold nb090_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_065 A) ≠
        (nb090_alpha_dummy_069 A) from (by
          unfold nb090_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A)
                  0)))) (show (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from (by
          unfold nb090_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A),
        (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
        ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_072
        A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)), ((nb090_alpha_dummy_057 A),
        (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
        ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A)
                                        from (by
                                          unfold nb090_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0054 A) 0)))) (show
                                        (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h)
                                        from (by
                                          unfold nb090_alpha_dummy_070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0055 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                      ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                      ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                      ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                      ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                      ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
                                      ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                      ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                      (by
                                        unfold nb090_alpha_dummy_069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0054 A)
                                                0)))) (show (nb090_alpha_dummy_067 h) ≠
                                        (nb090_alpha_dummy_070 h) from (by
                                        unfold nb090_alpha_dummy_070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0055 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A)
                                        from (by
                                          unfold nb090_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0054 A) 0)))) (show
                                        (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h)
                                        from (by
                                          unfold nb090_alpha_dummy_070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0055 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                      ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                      ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                      ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                      ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                      ((nb090_alpha_dummy_063 A), (nb090_alpha_dummy_064 h)),
                                      ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                      ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part026`. -/


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
noncomputable def nb090_split_alpha_0002 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)),
        ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
        ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)),
        ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classMem (Class.cv (nb090_alpha_dummy_089 A))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_090 h))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_065 A) from (by
                            unfold nb090_alpha_dummy_065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                        (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_067 h) from (by
                            unfold nb090_alpha_dummy_067;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_066 A) from (by
                              unfold nb090_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                          (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_068 h) from (by
                              unfold nb090_alpha_dummy_068;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_091 A) from (by
                                unfold nb090_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0082 A) 0))))
                            (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_092 h) from (by
                                unfold nb090_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0083 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_089 A) from
                                (by
                                  unfold nb090_alpha_dummy_089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0080 A) 0))))
                              (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_090 h) from
                                (by
                                  unfold nb090_alpha_dummy_090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0081 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_065 A) ≠
        (nb090_alpha_dummy_072 A) from (by
          unfold nb090_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_075 h) from (by
          unfold nb090_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_071 A) from (by
          unfold nb090_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 0)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_074 h) from (by
          unfold nb090_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from (by
          unfold nb090_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A) 0)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_070 h) from (by
          unfold nb090_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A),
        (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A),
        (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A),
        (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A),
        (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_072
        A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                    (by
                                      unfold nb090_alpha_dummy_069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from
                                    (by
                                      unfold nb090_alpha_dummy_070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                  ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                  ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                  ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)),
                                  ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)),
                                  ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                  ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                  ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)),
                                  ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                  ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                  ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                  ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                  ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                  ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from (by
                                    unfold nb090_alpha_dummy_069;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0054 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from (by
                                    unfold nb090_alpha_dummy_070;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0055 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                    (by
                                      unfold nb090_alpha_dummy_069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from
                                    (by
                                      unfold nb090_alpha_dummy_070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                  ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                  ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                  ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)),
                                  ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)),
                                  ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                  ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                  ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)),
                                  ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                  ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                  ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                  ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                  ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                  ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_065 A) from (by
                            unfold nb090_alpha_dummy_065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                        (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_067 h) from (by
                            unfold nb090_alpha_dummy_067;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_066 A) from (by
                              unfold nb090_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                          (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_068 h) from (by
                              unfold nb090_alpha_dummy_068;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_091 A) from (by
                                unfold nb090_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0082 A) 0))))
                            (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_092 h) from (by
                                unfold nb090_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0083 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_058 A) ≠ (nb090_alpha_dummy_089 A) from
                                (by
                                  unfold nb090_alpha_dummy_089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0080 A) 0))))
                              (show (nb090_alpha_dummy_060 h) ≠ (nb090_alpha_dummy_090 h) from
                                (by
                                  unfold nb090_alpha_dummy_090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0081 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_065 A) ≠
        (nb090_alpha_dummy_072 A) from (by
          unfold nb090_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_075 h) from (by
          unfold nb090_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_071 A) from (by
          unfold nb090_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 0)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_074 h) from (by
          unfold nb090_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from (by
          unfold nb090_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A) 0)))) (show (nb090_alpha_dummy_067 h) ≠
        (nb090_alpha_dummy_070 h) from (by
          unfold nb090_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A),
        (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A),
        (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠ (nb090_alpha_dummy_079 A) from (by
          unfold
            nb090_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_080 h) from (by
          unfold
            nb090_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_077 A) from (by
          unfold
            nb090_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_078 h) from (by
          unfold
            nb090_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_073 A), (nb090_alpha_dummy_076 h)), ((nb090_alpha_dummy_072 A),
        (nb090_alpha_dummy_075 h)), ((nb090_alpha_dummy_071 A), (nb090_alpha_dummy_074 h)),
        ((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)), ((nb090_alpha_dummy_065 A),
        (nb090_alpha_dummy_067 h)), ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
        ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)), ((nb090_alpha_dummy_089 A),
        (nb090_alpha_dummy_090 h)), ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
        ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)), ((nb090_alpha_dummy_087 A),
        (nb090_alpha_dummy_088 h)), ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_072
        A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_083 A) from (by
          unfold
            nb090_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_084 h) from (by
          unfold
            nb090_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_072 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_065
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_073
        A) ≠ (nb090_alpha_dummy_085 A) from (by
          unfold
            nb090_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_086 h) from (by
          unfold
            nb090_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_073 A) ≠
        (nb090_alpha_dummy_081 A) from (by
          unfold
            nb090_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090_alpha_dummy_076 h) ≠ (nb090_alpha_dummy_082 h) from (by
          unfold
            nb090_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                    (by
                                      unfold nb090_alpha_dummy_069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from
                                    (by
                                      unfold nb090_alpha_dummy_070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                  ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                  ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                  ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)),
                                  ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)),
                                  ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                  ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                  ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)),
                                  ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                  ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                  ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                  ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                  ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                  ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from (by
                                    unfold nb090_alpha_dummy_069;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0054 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from (by
                                    unfold nb090_alpha_dummy_070;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0055 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_069 A) from
                                    (by
                                      unfold nb090_alpha_dummy_069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_070 h) from
                                    (by
                                      unfold nb090_alpha_dummy_070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_069 A), (nb090_alpha_dummy_070 h)),
                                  ((nb090_alpha_dummy_065 A), (nb090_alpha_dummy_067 h)),
                                  ((nb090_alpha_dummy_066 A), (nb090_alpha_dummy_068 h)),
                                  ((nb090_alpha_dummy_091 A), (nb090_alpha_dummy_092 h)),
                                  ((nb090_alpha_dummy_089 A), (nb090_alpha_dummy_090 h)),
                                  ((nb090_alpha_dummy_058 A), (nb090_alpha_dummy_060 h)),
                                  ((nb090_alpha_dummy_057 A), (nb090_alpha_dummy_059 h)),
                                  ((nb090_alpha_dummy_087 A), (nb090_alpha_dummy_088 h)),
                                  ((nb090_alpha_dummy_061 A), (nb090_alpha_dummy_062 h)),
                                  ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                  ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                  ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                  ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                  ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part027`. -/


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
noncomputable def nb090_split_alpha_0003 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_099 A))
          (Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_099 A))
            (Class.cab (nb090_alpha_dummy_093 A)
              (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_100 h))
          (Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_100 h))
            (Class.cab (nb090_alpha_dummy_095 h)
              (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_094 A) from (by
                      unfold nb090_alpha_dummy_094;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
                  (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_096 h) from (by
                      unfold nb090_alpha_dummy_096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_093 A) from (by
                        unfold nb090_alpha_dummy_093;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
                    (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_095 h) from (by
                        unfold nb090_alpha_dummy_095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0086 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_099 A) from (by
                          unfold nb090_alpha_dummy_099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0088 A) 0))))
                      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_100 h) from (by
                          unfold nb090_alpha_dummy_100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0089 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_097 A) from (by
                            unfold nb090_alpha_dummy_097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0085 A) 0))))
                        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_098 h) from (by
                            unfold nb090_alpha_dummy_098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0087 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
                              ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
                                ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_051 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_054 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_101 A) from (by
                              unfold nb090_alpha_dummy_101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                          (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_103 h) from (by
                              unfold nb090_alpha_dummy_103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0091 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_102 A) from (by
                                unfold nb090_alpha_dummy_102;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                            (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_104 h) from (by
                                unfold nb090_alpha_dummy_104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0091 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_108 A) from (by
          unfold nb090_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 1)))) (show (nb090_alpha_dummy_103 h) ≠
        (nb090_alpha_dummy_111 h) from (by
          unfold nb090_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_107 A) from (by
          unfold nb090_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 0)))) (show (nb090_alpha_dummy_103 h) ≠
        (nb090_alpha_dummy_110 h) from (by
          unfold nb090_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from (by
          unfold nb090_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A)
                  0)))) (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from (by
          unfold nb090_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A),
        (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)),
        ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A),
        (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A),
        (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A),
        (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)),
        ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A),
        (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A),
        (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_108
        A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_109
        A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_109
        A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from
                                      (by
                                        unfold nb090_alpha_dummy_105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0092 A)
                                                0)))) (show (nb090_alpha_dummy_103 h) ≠
                                        (nb090_alpha_dummy_106 h) from (by
                                        unfold nb090_alpha_dummy_106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0093 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                                    ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                                    ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                                    ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                                    ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                                    ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
                                    ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                    ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from
                                    (by
                                      unfold nb090_alpha_dummy_105;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0092 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from
                                    (by
                                      unfold nb090_alpha_dummy_106;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0093 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from
                                      (by
                                        unfold nb090_alpha_dummy_105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0092 A)
                                                0)))) (show (nb090_alpha_dummy_103 h) ≠
                                        (nb090_alpha_dummy_106 h) from (by
                                        unfold nb090_alpha_dummy_106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0093 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                                    ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                                    ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                                    ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                                    ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                                    ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
                                    ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                    ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_094 A) from (by
                        unfold nb090_alpha_dummy_094;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
                    (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_096 h) from (by
                        unfold nb090_alpha_dummy_096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0086 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_093 A) from (by
                          unfold nb090_alpha_dummy_093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
                      (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_095 h) from (by
                          unfold nb090_alpha_dummy_095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0086 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_099 A) from (by
                            unfold nb090_alpha_dummy_099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0088 A) 0))))
                        (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_100 h) from (by
                            unfold nb090_alpha_dummy_100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0089 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_097 A) from (by
                              unfold nb090_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0085 A) 0))))
                          (show (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_098 h) from (by
                              unfold nb090_alpha_dummy_098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0087 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
                                ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
                                  ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_051 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_054 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_101 A) from (by
                                unfold nb090_alpha_dummy_101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                            (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_103 h) from (by
                                unfold nb090_alpha_dummy_103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0091 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_102 A) from
                                (by
                                  unfold nb090_alpha_dummy_102;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                              (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_104 h) from
                                (by
                                  unfold nb090_alpha_dummy_104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0091 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_094 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_096 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_108 A) from (by
          unfold nb090_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 1)))) (show (nb090_alpha_dummy_103 h) ≠
        (nb090_alpha_dummy_111 h) from (by
          unfold nb090_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_107 A) from (by
          unfold nb090_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A)
                  0)))) (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_110 h) from (by
          unfold nb090_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_101 A) ≠
        (nb090_alpha_dummy_105 A) from (by
          unfold nb090_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A)
                  0)))) (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from (by
          unfold nb090_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A),
        (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)),
        ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A),
        (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A),
        (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A),
        (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)),
        ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A),
        (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A),
        (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_108
        A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_109
        A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_109
        A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A)
                                        from (by
                                          unfold nb090_alpha_dummy_105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0092 A) 0)))) (show
                                        (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h)
                                        from (by
                                          unfold nb090_alpha_dummy_106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0093 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                                      ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                                      ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                                      ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                                      ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                                      ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
                                      ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                      ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from
                                      (by
                                        unfold nb090_alpha_dummy_105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0092 A)
                                                0)))) (show (nb090_alpha_dummy_103 h) ≠
                                        (nb090_alpha_dummy_106 h) from (by
                                        unfold nb090_alpha_dummy_106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0093 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A)
                                        from (by
                                          unfold nb090_alpha_dummy_105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0092 A) 0)))) (show
                                        (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h)
                                        from (by
                                          unfold nb090_alpha_dummy_106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0093 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                                      ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                                      ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                                      ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                                      ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                                      ((nb090_alpha_dummy_099 A), (nb090_alpha_dummy_100 h)),
                                      ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                      ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
