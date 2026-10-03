/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C096M3Part002

/-! NF weak partition development: NAR4H5C096M3Part003. -/


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
noncomputable def nb096_split_alpha_0003 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_071 D R))
          (Class.cab (nb096_alpha_dummy_065 D R)
            (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_071 D R))
            (Class.cab (nb096_alpha_dummy_065 D R)
              (syn_wrex (nb096_alpha_dummy_066 D R) (Class.cv (nb096_alpha_dummy_052 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_072 R q))
          (Class.cab (nb096_alpha_dummy_067 R q)
            (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_072 R q))
            (Class.cab (nb096_alpha_dummy_067 R q)
              (syn_wrex (nb096_alpha_dummy_068 R q) (Class.cv (nb096_alpha_dummy_054 R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_067 R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_066 D R) from (by
                      unfold nb096_alpha_dummy_066;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
                  (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
                      unfold nb096_alpha_dummy_068;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0062 R q) 1)))) (TAlphaVar.there
                    (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_065 D R) from (by
                        unfold nb096_alpha_dummy_065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
                    (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
                        unfold nb096_alpha_dummy_067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
                    (TAlphaVar.there
                      (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_071 D R) from (by
                          unfold nb096_alpha_dummy_071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0064 D R) 0))))
                      (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_072 R q) from (by
                          unfold nb096_alpha_dummy_072;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0065 R q) 0))))
                      (TAlphaVar.there
                        (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_069 D R) from (by
                            unfold nb096_alpha_dummy_069;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0061 D R) 0))))
                        (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_070 R q) from (by
                            unfold nb096_alpha_dummy_070;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0063 R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
                      ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
                      ((Class.cv (nb096_alpha_dummy_053 R q))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_073 D R) from
                            (by
                              unfold nb096_alpha_dummy_073;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0066 D R) 0))))
                          (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_075 R q) from
                            (by
                              unfold nb096_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0067 R q) 0))))
                          (TAlphaVar.there (show
                              (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_074 D R) from (by
                                unfold nb096_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0066 D R) 1)))) (show
                              (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_076 R q) from (by
                                unfold nb096_alpha_dummy_076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0067 R q) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_080 D R) from
        (by
          unfold nb096_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R) 1)))) (show (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_083 R q) from (by
          unfold nb096_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q) 1)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_079 D R) from (by
          unfold nb096_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R)
                  0)))) (show (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_082 R q) from (by
          unfold nb096_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_077 D R) from (by
          unfold nb096_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R)
                  0)))) (show (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from (by
          unfold nb096_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)),
        ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)),
        ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)),
        ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
        ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
        ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
        ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
        ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
        ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)),
        ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)),
        ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)),
        ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
        ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
        ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
        ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
        ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
        ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R
        q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_091 D R) from
        (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_091 D R) from
        (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081
        D R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081
        D R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R)
                                      from (by
                                        unfold nb096_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0068 D R) 0)))) (show
                                      (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q)
                                      from (by
                                        unfold nb096_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0069 R q) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                                    ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
                                    ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
                                    ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
                                    ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
                                    ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
                                    ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
                                    ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
                                    ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
                                    ((nb096_alpha_dummy_049 D R),
                                      (nb096_alpha_dummy_050 D R q)),
                                    ((nb096_alpha_dummy_047 D R),
                                      (nb096_alpha_dummy_048 D R q)),
                                    ((nb096_alpha_dummy_045 D R),
                                      (nb096_alpha_dummy_046 D R q)),
                                    ((nb096_alpha_dummy_042 D R),
                                      (nb096_alpha_dummy_044 D R q)),
                                    ((nb096_alpha_dummy_041 D R),
                                      (nb096_alpha_dummy_043 D R q)),
                                    ((nb096_alpha_dummy_001 D R),
                                      (nb096_alpha_dummy_002 D R q)),
                                    ((nb096_alpha_dummy_000 D R), q),
                                    ((nb096_alpha_dummy_003 D R),
                                      (nb096_alpha_dummy_004 D R q))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R)
                                    from (by
                                      unfold nb096_alpha_dummy_077;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0068 D R)
                                              0)))) (show (nb096_alpha_dummy_075 R q) ≠
                                      (nb096_alpha_dummy_078 R q) from (by
                                      unfold nb096_alpha_dummy_078;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0069 R q)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R)
                                      from (by
                                        unfold nb096_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0068 D R) 0)))) (show
                                      (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q)
                                      from (by
                                        unfold nb096_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0069 R q) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                                    ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
                                    ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
                                    ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
                                    ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
                                    ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
                                    ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
                                    ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
                                    ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
                                    ((nb096_alpha_dummy_049 D R),
                                      (nb096_alpha_dummy_050 D R q)),
                                    ((nb096_alpha_dummy_047 D R),
                                      (nb096_alpha_dummy_048 D R q)),
                                    ((nb096_alpha_dummy_045 D R),
                                      (nb096_alpha_dummy_046 D R q)),
                                    ((nb096_alpha_dummy_042 D R),
                                      (nb096_alpha_dummy_044 D R q)),
                                    ((nb096_alpha_dummy_041 D R),
                                      (nb096_alpha_dummy_043 D R q)),
                                    ((nb096_alpha_dummy_001 D R),
                                      (nb096_alpha_dummy_002 D R q)),
                                    ((nb096_alpha_dummy_000 D R), q),
                                    ((nb096_alpha_dummy_003 D R),
                                      (nb096_alpha_dummy_004 D R q))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_066 D R) from (by
                        unfold nb096_alpha_dummy_066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
                    (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
                        unfold nb096_alpha_dummy_068;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0062 R q) 1))))
                    (TAlphaVar.there
                      (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_065 D R) from (by
                          unfold nb096_alpha_dummy_065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
                      (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
                          unfold nb096_alpha_dummy_067;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
                      (TAlphaVar.there
                        (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_071 D R) from (by
                            unfold nb096_alpha_dummy_071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0064 D R) 0))))
                        (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_072 R q) from (by
                            unfold nb096_alpha_dummy_072;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0065 R q) 0))))
                        (TAlphaVar.there
                          (show (nb096_alpha_dummy_052 D R) ≠ (nb096_alpha_dummy_069 D R) from
                            (by
                              unfold nb096_alpha_dummy_069;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0061 D R) 0))))
                          (show (nb096_alpha_dummy_054 R q) ≠ (nb096_alpha_dummy_070 R q) from
                            (by
                              unfold nb096_alpha_dummy_070;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0063 R q) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
                        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪
                        ((Class.cv (nb096_alpha_dummy_053 R q))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_073 D R) from (by
                                unfold nb096_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0066 D R) 0)))) (show
                              (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_075 R q) from (by
                                unfold nb096_alpha_dummy_075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0067 R q) 0))))
                            (TAlphaVar.there (show
                                (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_074 D R) from
                                (by
                                  unfold nb096_alpha_dummy_074;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0066 D R)
                                          1)))) (show
                                (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_076 R q) from
                                (by
                                  unfold nb096_alpha_dummy_076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0067 R q)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_080 D R) from (by
          unfold nb096_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R)
                  1)))) (show (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_083 R q) from (by
          unfold nb096_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_079 D R) from (by
          unfold nb096_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R)
                  0)))) (show (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_082 R q) from (by
          unfold nb096_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_077 D R) from (by
          unfold nb096_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R)
                  0)))) (show (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from (by
          unfold nb096_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)),
        ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)),
        ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)),
        ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
        ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
        ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
        ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
        ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
        ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)),
        ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)),
        ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)),
        ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
        ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
        ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
        ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
        ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
        ((nb096_alpha_dummy_071 D R), (nb096_alpha_dummy_072 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R
        q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_091 D R) from
        (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_091 D R) from
        (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081
        D R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081
        D R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_077 D R) from (by
                                          unfold nb096_alpha_dummy_077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0068 D R) 0)))) (show
                                        (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_078 R q) from (by
                                          unfold nb096_alpha_dummy_078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0069 R q) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                                      ((nb096_alpha_dummy_073 D R),
                                        (nb096_alpha_dummy_075 R q)),
                                      ((nb096_alpha_dummy_074 D R),
                                        (nb096_alpha_dummy_076 R q)),
                                      ((nb096_alpha_dummy_066 D R),
                                        (nb096_alpha_dummy_068 R q)),
                                      ((nb096_alpha_dummy_065 D R),
                                        (nb096_alpha_dummy_067 R q)),
                                      ((nb096_alpha_dummy_071 D R),
                                        (nb096_alpha_dummy_072 R q)),
                                      ((nb096_alpha_dummy_069 D R),
                                        (nb096_alpha_dummy_070 R q)),
                                      ((nb096_alpha_dummy_052 D R),
                                        (nb096_alpha_dummy_054 R q)),
                                      ((nb096_alpha_dummy_051 D R),
                                        (nb096_alpha_dummy_053 R q)),
                                      ((nb096_alpha_dummy_049 D R),
                                        (nb096_alpha_dummy_050 D R q)),
                                      ((nb096_alpha_dummy_047 D R),
                                        (nb096_alpha_dummy_048 D R q)),
                                      ((nb096_alpha_dummy_045 D R),
                                        (nb096_alpha_dummy_046 D R q)),
                                      ((nb096_alpha_dummy_042 D R),
                                        (nb096_alpha_dummy_044 D R q)),
                                      ((nb096_alpha_dummy_041 D R),
                                        (nb096_alpha_dummy_043 D R q)),
                                      ((nb096_alpha_dummy_001 D R),
                                        (nb096_alpha_dummy_002 D R q)),
                                      ((nb096_alpha_dummy_000 D R), q),
                                      ((nb096_alpha_dummy_003 D R),
                                        (nb096_alpha_dummy_004 D R q))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R)
                                      from (by
                                        unfold nb096_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0068 D R) 0)))) (show
                                      (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q)
                                      from (by
                                        unfold nb096_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0069 R q) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_077 D R) from (by
                                          unfold nb096_alpha_dummy_077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0068 D R) 0)))) (show
                                        (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_078 R q) from (by
                                          unfold nb096_alpha_dummy_078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0069 R q) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                                      ((nb096_alpha_dummy_073 D R),
                                        (nb096_alpha_dummy_075 R q)),
                                      ((nb096_alpha_dummy_074 D R),
                                        (nb096_alpha_dummy_076 R q)),
                                      ((nb096_alpha_dummy_066 D R),
                                        (nb096_alpha_dummy_068 R q)),
                                      ((nb096_alpha_dummy_065 D R),
                                        (nb096_alpha_dummy_067 R q)),
                                      ((nb096_alpha_dummy_071 D R),
                                        (nb096_alpha_dummy_072 R q)),
                                      ((nb096_alpha_dummy_069 D R),
                                        (nb096_alpha_dummy_070 R q)),
                                      ((nb096_alpha_dummy_052 D R),
                                        (nb096_alpha_dummy_054 R q)),
                                      ((nb096_alpha_dummy_051 D R),
                                        (nb096_alpha_dummy_053 R q)),
                                      ((nb096_alpha_dummy_049 D R),
                                        (nb096_alpha_dummy_050 D R q)),
                                      ((nb096_alpha_dummy_047 D R),
                                        (nb096_alpha_dummy_048 D R q)),
                                      ((nb096_alpha_dummy_045 D R),
                                        (nb096_alpha_dummy_046 D R q)),
                                      ((nb096_alpha_dummy_042 D R),
                                        (nb096_alpha_dummy_044 D R q)),
                                      ((nb096_alpha_dummy_041 D R),
                                        (nb096_alpha_dummy_043 D R q)),
                                      ((nb096_alpha_dummy_001 D R),
                                        (nb096_alpha_dummy_002 D R q)),
                                      ((nb096_alpha_dummy_000 D R), q),
                                      ((nb096_alpha_dummy_003 D R),
                                        (nb096_alpha_dummy_004 D R q))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb096_split_alpha_0004 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)),
        ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)),
        ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
        ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
        ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_099 D R))
          (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_099 D R))
            (syn_cphi (Class.cv (nb096_alpha_dummy_066 D R))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_100 R q))
          (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_100 R q))
            (syn_cphi (Class.cv (nb096_alpha_dummy_068 R q)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_073 D R) from (by
                      unfold nb096_alpha_dummy_073;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0066 D R) 0))))
                  (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_075 R q) from (by
                      unfold nb096_alpha_dummy_075;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0067 R q) 0)))) (TAlphaVar.there
                    (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_074 D R) from (by
                        unfold nb096_alpha_dummy_074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0066 D R) 1))))
                    (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_076 R q) from (by
                        unfold nb096_alpha_dummy_076;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0067 R q) 1))))
                    (TAlphaVar.there
                      (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_099 D R) from (by
                          unfold nb096_alpha_dummy_099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0096 D R) 0))))
                      (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_100 R q) from (by
                          unfold nb096_alpha_dummy_100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0097 R q) 0))))
                      (TAlphaVar.there
                        (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_097 D R) from (by
                            unfold nb096_alpha_dummy_097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0094 D R) 0))))
                        (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_098 R q) from (by
                            unfold nb096_alpha_dummy_098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0095 R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_080 D R)
                                      from (by
                                        unfold nb096_alpha_dummy_080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0070 D R) 1)))) (show
                                      (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_083 R q)
                                      from (by
                                        unfold nb096_alpha_dummy_083;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0071 R q) 1))))
                                    (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_079 D R) from (by
                                          unfold nb096_alpha_dummy_079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0070 D R) 0)))) (show
                                        (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_082 R q) from (by
                                          unfold nb096_alpha_dummy_082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0071 R q) 0))))
                                      (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_077 D R) from (by
          unfold nb096_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R) 0)))) (show (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_078 R q) from (by
          unfold nb096_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb096_alpha_dummy_081 D R),
        (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R),
        (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R),
        (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R),
        (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R),
        (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R),
        (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R),
        (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R),
        (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R),
        (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R),
        (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R),
        (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R),
        (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R),
        (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R),
        (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R),
        (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R),
        (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R),
        (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R),
        (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R),
        (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
                                        ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_087 D R) from (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_087 D R) from (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb096_alpha_dummy_081 D R),
        (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R),
        (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R),
        (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R),
        (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R),
        (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R),
        (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R),
        (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R),
        (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R),
        (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R),
        (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R),
        (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R),
        (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R),
        (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R),
        (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R),
        (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R),
        (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R),
        (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R),
        (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R),
        (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_091 D R) from (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_091 D R) from (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from (by
                                unfold nb096_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)))) (show
                              (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from (by
                                unfold nb096_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                            ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
                            ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
                            ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)),
                            ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)),
                            ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
                            ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
                            ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)),
                            ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
                            ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
                            ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
                            ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
                            ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
                            ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
                            ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
                            ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
                            ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                            ((nb096_alpha_dummy_000 D R), q),
                            ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from
                            (by
                              unfold nb096_alpha_dummy_077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0068 D R) 0))))
                          (show (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from
                            (by
                              unfold nb096_alpha_dummy_078;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from (by
                                unfold nb096_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)))) (show
                              (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from (by
                                unfold nb096_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                            ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
                            ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
                            ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)),
                            ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)),
                            ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
                            ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
                            ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)),
                            ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
                            ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
                            ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
                            ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
                            ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
                            ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
                            ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
                            ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
                            ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                            ((nb096_alpha_dummy_000 D R), q),
                            ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_073 D R) from (by
                        unfold nb096_alpha_dummy_073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0066 D R) 0))))
                    (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_075 R q) from (by
                        unfold nb096_alpha_dummy_075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0067 R q) 0))))
                    (TAlphaVar.there
                      (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_074 D R) from (by
                          unfold nb096_alpha_dummy_074;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0066 D R) 1))))
                      (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_076 R q) from (by
                          unfold nb096_alpha_dummy_076;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0067 R q) 1))))
                      (TAlphaVar.there
                        (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_099 D R) from (by
                            unfold nb096_alpha_dummy_099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0096 D R) 0))))
                        (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_100 R q) from (by
                            unfold nb096_alpha_dummy_100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0097 R q) 0))))
                        (TAlphaVar.there
                          (show (nb096_alpha_dummy_066 D R) ≠ (nb096_alpha_dummy_097 D R) from
                            (by
                              unfold nb096_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0094 D R) 0))))
                          (show (nb096_alpha_dummy_068 R q) ≠ (nb096_alpha_dummy_098 R q) from
                            (by
                              unfold nb096_alpha_dummy_098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0095 R q) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb096_alpha_dummy_066 D R))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb096_alpha_dummy_068 R q))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_080 D R) from (by
                                          unfold nb096_alpha_dummy_080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0070 D R) 1)))) (show
                                        (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_083 R q) from (by
                                          unfold nb096_alpha_dummy_083;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0071 R q) 1))))
                                      (TAlphaVar.there (show (nb096_alpha_dummy_073 D R) ≠
        (nb096_alpha_dummy_079 D R) from (by
          unfold nb096_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R) 0)))) (show (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_082 R q) from (by
          unfold nb096_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from (by
          unfold nb096_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R) 0)))) (show (nb096_alpha_dummy_075 R q) ≠
        (nb096_alpha_dummy_078 R q) from (by
          unfold nb096_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb096_alpha_dummy_081 D R),
        (nb096_alpha_dummy_084 R q)), ((nb096_alpha_dummy_080 D R),
        (nb096_alpha_dummy_083 R q)), ((nb096_alpha_dummy_079 D R),
        (nb096_alpha_dummy_082 R q)), ((nb096_alpha_dummy_077 D R),
        (nb096_alpha_dummy_078 R q)), ((nb096_alpha_dummy_073 D R),
        (nb096_alpha_dummy_075 R q)), ((nb096_alpha_dummy_074 D R),
        (nb096_alpha_dummy_076 R q)), ((nb096_alpha_dummy_099 D R),
        (nb096_alpha_dummy_100 R q)), ((nb096_alpha_dummy_097 D R),
        (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D R),
        (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R),
        (nb096_alpha_dummy_067 R q)), ((nb096_alpha_dummy_095 D R),
        (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069 D R),
        (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R),
        (nb096_alpha_dummy_054 R q)), ((nb096_alpha_dummy_051 D R),
        (nb096_alpha_dummy_053 R q)), ((nb096_alpha_dummy_049 D R),
        (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D R),
        (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R),
        (nb096_alpha_dummy_046 D R q)), ((nb096_alpha_dummy_042 D R),
        (nb096_alpha_dummy_044 D R q)), ((nb096_alpha_dummy_041 D R),
        (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D R),
        (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_080 D
        R) ≠ (nb096_alpha_dummy_087 D R) from (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠ (nb096_alpha_dummy_087 D R) from
        (by
          unfold
            nb096_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_088 R q) from (by
          unfold
            nb096_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_085 D R) from (by
          unfold
            nb096_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_086 R q) from (by
          unfold
            nb096_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_081 D R), (nb096_alpha_dummy_084 R q)),
        ((nb096_alpha_dummy_080 D R), (nb096_alpha_dummy_083 R q)),
        ((nb096_alpha_dummy_079 D R), (nb096_alpha_dummy_082 R q)),
        ((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
        ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
        ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
        ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)),
        ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)),
        ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
        ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
        ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)),
        ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
        ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_080 D
        R) ≠ (nb096_alpha_dummy_091 D R) from (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠ (nb096_alpha_dummy_091 D R) from
        (by
          unfold
            nb096_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_092 R q) from (by
          unfold
            nb096_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_080 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096_alpha_dummy_083 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_075 R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081 D
        R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_081 D
        R) ≠ (nb096_alpha_dummy_093 D R) from (by
          unfold
            nb096_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_094 R q) from (by
          unfold
            nb096_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_081 D R) ≠
        (nb096_alpha_dummy_089 D R) from (by
          unfold
            nb096_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096_alpha_dummy_084 R q) ≠ (nb096_alpha_dummy_090 R q) from (by
          unfold
            nb096_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from
                                (by
                                  unfold nb096_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0068 D R)
                                          0)))) (show
                                (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from
                                (by
                                  unfold nb096_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0069 R q)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                              ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
                              ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
                              ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)),
                              ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)),
                              ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
                              ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
                              ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)),
                              ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
                              ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
                              ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
                              ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
                              ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
                              ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
                              ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
                              ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
                              ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                              ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
                                (nb096_alpha_dummy_004 D R q))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from (by
                                unfold nb096_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)))) (show
                              (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from (by
                                unfold nb096_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb096_alpha_dummy_073 D R) ≠ (nb096_alpha_dummy_077 D R) from
                                (by
                                  unfold nb096_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0068 D R)
                                          0)))) (show
                                (nb096_alpha_dummy_075 R q) ≠ (nb096_alpha_dummy_078 R q) from
                                (by
                                  unfold nb096_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0069 R q)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb096_alpha_dummy_077 D R), (nb096_alpha_dummy_078 R q)),
                              ((nb096_alpha_dummy_073 D R), (nb096_alpha_dummy_075 R q)),
                              ((nb096_alpha_dummy_074 D R), (nb096_alpha_dummy_076 R q)),
                              ((nb096_alpha_dummy_099 D R), (nb096_alpha_dummy_100 R q)),
                              ((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)),
                              ((nb096_alpha_dummy_066 D R), (nb096_alpha_dummy_068 R q)),
                              ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R q)),
                              ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)),
                              ((nb096_alpha_dummy_069 D R), (nb096_alpha_dummy_070 R q)),
                              ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
                              ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
                              ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
                              ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
                              ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
                              ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
                              ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
                              ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                              ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
                                (nb096_alpha_dummy_004 D R q))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb096_focused_notmem_0015 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0250 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_052, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0015 D R) (nb096_compact_fv_empty_0052 D R))

theorem nb096_focused_notmem_0016 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0251 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_054, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0016 R q) (nb096_compact_fv_empty_0053 R q))

theorem nb096_focused_notmem_0017 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0252 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_051, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0017 D R) (nb096_compact_fv_empty_0054 D R))

theorem nb096_focused_notmem_0018 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv q))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0253 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_053, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0018 R q) (nb096_compact_fv_empty_0055 R q))

theorem nb096_focused_notmem_0019 (D : Class) (R : Class) :
    (nb096_alpha_dummy_049 D R) ∉ R.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0254 (D : Class) (R : Class) :
    (nb096_alpha_dummy_049 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_049, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0019 D R) (nb096_compact_fv_empty_0056 D R))

theorem nb096_focused_notmem_0020 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_050 D R q) ∉ R.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0255 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_050 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_050, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0020 D R q) (nb096_compact_fv_empty_0057 D R q))

theorem nb096_focused_notmem_0021 (D : Class) (R : Class) :
    (nb096_alpha_dummy_047 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0256 (D : Class) (R : Class) :
    (nb096_alpha_dummy_047 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_047, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0021 D R) (nb096_compact_fv_empty_0058 D R))

theorem nb096_focused_notmem_0022 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_048 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0257 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_048 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_048, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0022 D R q) (nb096_compact_fv_empty_0059 D R q))

theorem nb096_focused_notmem_0023 (D : Class) (R : Class) :
    (nb096_alpha_dummy_045 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0258 (D : Class) (R : Class) :
    (nb096_alpha_dummy_045 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_045, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0023 D R) (nb096_compact_fv_empty_0060 D R))

theorem nb096_focused_notmem_0024 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_046 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

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

theorem nb096_wpp_notmem_0259 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_046 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_046, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0024 D R q) (nb096_compact_fv_empty_0061 D R q))

theorem nb096_focused_notmem_0025 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0260 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0025 D R) (nb096_compact_fv_empty_0062 D R))

theorem nb096_focused_notmem_0026 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0261 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0026 D R q) (nb096_compact_fv_empty_0063 D R q))

theorem nb096_focused_notmem_0027 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0262 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0027 D R) (nb096_compact_fv_empty_0064 D R))

theorem nb096_focused_notmem_0028 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0263 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0028 D R q) (nb096_compact_fv_empty_0065 D R q))

theorem nb096_focused_notmem_0029 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb096_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0264 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0029 D R) (nb096_compact_fv_empty_0020 D R))

theorem nb096_focused_notmem_0030 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0265 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0030 D R q) (nb096_compact_fv_empty_0021 D R q))

theorem nb096_focused_notmem_0031 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_wpp_notmem_0266 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0031 D R) (nb096_compact_fv_empty_0022 D R))

theorem nb096_wpp_notmem_0267 (R : Class) (q : Var) (dv_R_q : q ∉ R.fv) :
    q ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_R_q (nb096_compact_fv_empty_0023 q))

theorem nb096_focused_notmem_0032 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉ R.fv :=
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
      R.fv
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
  right
  rw [fv_wff_classEq (Class.cv (nb096_alpha_dummy_001 D R))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0268 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0032 D R) (nb096_compact_fv_empty_0024 D R))

theorem nb096_focused_notmem_0033 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ({(nb096_alpha_dummy_002 D R q)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv q) (syn_cpw1 (syn_cpw1 D)))
      (Wff.classEq (Class.cv (nb096_alpha_dummy_002 D R q)) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb096_alpha_dummy_002 D R q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0269 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0033 D R q) (nb096_compact_fv_empty_0025 D R q))

theorem nb096_compact_envfresh_0016 (D : Class) (R : Class) (q : Var)
    (dv_R_q : q ∉ R.fv) :
    TEnvFresh
      [((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096_alpha_dummy_052 D R) (nb096_alpha_dummy_054 R q)
      (nb096_wpp_notmem_0250 D R) (nb096_wpp_notmem_0251 R q)
      (TEnvFresh.consFresh (nb096_alpha_dummy_051 D R) (nb096_alpha_dummy_053 R q)
        (nb096_wpp_notmem_0252 D R) (nb096_wpp_notmem_0253 R q)
        (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q)
          (nb096_wpp_notmem_0254 D R) (nb096_wpp_notmem_0255 D R q)
          (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q)
            (nb096_wpp_notmem_0256 D R) (nb096_wpp_notmem_0257 D R q)
            (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q)
              (nb096_wpp_notmem_0258 D R) (nb096_wpp_notmem_0259 D R q)
              (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R)
                (nb096_alpha_dummy_044 D R q) (nb096_wpp_notmem_0260 D R)
                (nb096_wpp_notmem_0261 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R)
                  (nb096_alpha_dummy_043 D R q) (nb096_wpp_notmem_0262 D R)
                  (nb096_wpp_notmem_0263 D R q) (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R)
                    (nb096_alpha_dummy_002 D R q) (nb096_wpp_notmem_0264 D R)
                    (nb096_wpp_notmem_0265 D R q)
                    (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q
                      (nb096_wpp_notmem_0266 D R) (nb096_wpp_notmem_0267 R q dv_R_q)
                      (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R)
                        (nb096_alpha_dummy_004 D R q) (nb096_wpp_notmem_0268 D R)
                        (nb096_wpp_notmem_0269 D R q)
                        (TEnvFresh.nil ((syn_ccnv (syn_cdif R (syn_cid)))).fv)))))))))))

@[expose]
noncomputable def nb096_wpp_refl_0015 (D : Class) (R : Class) (q : Var)
    (dv_R_q : q ∉ R.fv) :
    TReflOn
      [((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0016 D R q dv_R_q)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
