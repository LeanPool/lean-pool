/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C070C001Block001

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
noncomputable def nb070_split_alpha_0004 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
        ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
        ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)),
        ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
        ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
        ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
        ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
        ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_032 A))
          (Class.cv (nb070_alpha_dummy_025 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb070_alpha_dummy_033 A))
            (syn_cif (Wff.classMem (Class.cv (nb070_alpha_dummy_032 A)) (syn_cnnc))
              (syn_cplc (Class.cv (nb070_alpha_dummy_032 A)) (syn_c1c))
              (Class.cv (nb070_alpha_dummy_032 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_034 x))
          (Class.cv (nb070_alpha_dummy_027 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb070_alpha_dummy_035 x))
            (syn_cif (Wff.classMem (Class.cv (nb070_alpha_dummy_034 x)) (syn_cnnc))
              (syn_cplc (Class.cv (nb070_alpha_dummy_034 x)) (syn_c1c))
              (Class.cv (nb070_alpha_dummy_034 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb070_alpha_dummy_025 A) ≠ (nb070_alpha_dummy_032 A) from (by
              unfold nb070_alpha_dummy_032;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 0))))
          (show (nb070_alpha_dummy_027 x) ≠ (nb070_alpha_dummy_034 x) from (by
              unfold nb070_alpha_dummy_034;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 0))))
          (TAlphaVar.there (show (nb070_alpha_dummy_025 A) ≠ (nb070_alpha_dummy_033 A) from (by
                unfold nb070_alpha_dummy_033;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 1))))
            (show (nb070_alpha_dummy_027 x) ≠ (nb070_alpha_dummy_035 x) from (by
                unfold nb070_alpha_dummy_035;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 1))))
            (TAlphaVar.there (show (nb070_alpha_dummy_025 A) ≠ (nb070_alpha_dummy_058 A) from
                (by
                  unfold nb070_alpha_dummy_058;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0054 A) 0))))
              (show (nb070_alpha_dummy_027 x) ≠ (nb070_alpha_dummy_059 x) from (by
                  unfold nb070_alpha_dummy_059;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0055 x) 0))))
              (TAlphaVar.there (show (nb070_alpha_dummy_025 A) ≠ (nb070_alpha_dummy_056 A) from
                  (by
                    unfold nb070_alpha_dummy_056;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0052 A) 0))))
                (show (nb070_alpha_dummy_027 x) ≠ (nb070_alpha_dummy_057 x) from (by
                    unfold nb070_alpha_dummy_057;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0053 x) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb070_alpha_dummy_025 A))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb070_alpha_dummy_027 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_039 A) from
                                (by
                                  unfold nb070_alpha_dummy_039;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0028 A) 1))))
                              (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_042 x) from
                                (by
                                  unfold nb070_alpha_dummy_042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0029 x) 1))))
                              (TAlphaVar.there (show
                                  (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_038 A) from (by
                                    unfold nb070_alpha_dummy_038;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb070_support_mem_0028 A)
                                            0)))) (show
                                  (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_041 x) from (by
                                    unfold nb070_alpha_dummy_041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb070_support_mem_0029 x)
                                            0)))) (TAlphaVar.there (show
                                    (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from
                                    (by
                                      unfold nb070_alpha_dummy_036;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0026 A)
                                              0)))) (show
                                    (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from
                                    (by
                                      unfold nb070_alpha_dummy_037;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0027 x)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)),
                                  ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)),
                                  ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)),
                                  ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
                                  ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
                                  ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
                                  ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)),
                                  ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
                                  ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                                  ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                                  ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
                                  ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                                  ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                                  ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                                  ((nb070_alpha_dummy_001 A), x),
                                  ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A),
                                    (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A),
                                    (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A),
                                    (nb070_alpha_dummy_006 x A b))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb070_split_alpha_0003 x A b))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from (by
                          unfold nb070_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                      (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from (by
                          unfold nb070_alpha_dummy_037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
                      ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
                      ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
                      ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)),
                      ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
                      ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                      ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                      ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
                      ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                      ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                      ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                      ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                      ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                      ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                      ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from (by
                        unfold nb070_alpha_dummy_036;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                    (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from (by
                        unfold nb070_alpha_dummy_037;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from (by
                          unfold nb070_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                      (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from (by
                          unfold nb070_alpha_dummy_037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
                      ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
                      ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
                      ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)),
                      ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
                      ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                      ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                      ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
                      ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                      ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                      ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                      ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                      ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                      ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                      ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb070_split_alpha_0005 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
        ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_054 A))
          (Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb070_alpha_dummy_054 A))
            (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_055 x))
          (Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb070_alpha_dummy_055 x))
            (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_025 A) from (by
                      unfold nb070_alpha_dummy_025;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 1))))
                  (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_027 x) from (by
                      unfold nb070_alpha_dummy_027;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 1))))
                  (TAlphaVar.there
                    (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_024 A) from (by
                        unfold nb070_alpha_dummy_024;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0046 A) 0))))
                    (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_026 x) from (by
                        unfold nb070_alpha_dummy_026;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0048 x) 0)))) (TAlphaVar.there
                      (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_054 A) from (by
                          unfold nb070_alpha_dummy_054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0050 A) 0))))
                      (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_055 x) from (by
                          unfold nb070_alpha_dummy_055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0051 x) 0))))
                      (TAlphaVar.there
                        (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_028 A) from (by
                            unfold nb070_alpha_dummy_028;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0047 A) 0))))
                        (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_029 x) from (by
                            unfold nb070_alpha_dummy_029;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0049 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn
                                  (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv)
                            (by decide)) (freshVar_injective
                            (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪
                      ((Class.cv (nb070_alpha_dummy_008 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪
                      ((Class.cv (nb070_alpha_dummy_010 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb070_split_alpha_0004 x A b)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb070_split_alpha_0004 x A b)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
                          ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                          ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                          ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
                          ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                          ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                          ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                          ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                          ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                          ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                          ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_025 A) from (by
                        unfold nb070_alpha_dummy_025;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0046 A) 1))))
                    (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_027 x) from (by
                        unfold nb070_alpha_dummy_027;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0048 x) 1)))) (TAlphaVar.there
                      (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_024 A) from (by
                          unfold nb070_alpha_dummy_024;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0046 A) 0))))
                      (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_026 x) from (by
                          unfold nb070_alpha_dummy_026;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0048 x) 0))))
                      (TAlphaVar.there
                        (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_054 A) from (by
                            unfold nb070_alpha_dummy_054;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0050 A) 0))))
                        (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_055 x) from (by
                            unfold nb070_alpha_dummy_055;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0051 x) 0))))
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_028 A) from (by
                              unfold nb070_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0047 A) 0))))
                          (show (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_029 x) from (by
                              unfold nb070_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0049 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn
                                    (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv)
                              (by decide)) (freshVar_injective
                              (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪
                        ((Class.cv (nb070_alpha_dummy_008 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪
                        ((Class.cv (nb070_alpha_dummy_010 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb070_split_alpha_0004 x A b)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb070_split_alpha_0004 x A b)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
                            ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                            ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                            ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
                            ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                            ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                            ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                            ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                            ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                            ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                            ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb070_wpp_notmem_0162 (A : Class) : (nb070_alpha_dummy_009 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_009, fv_syn_cen] using (nb070_compact_fv_empty_0014 A)

theorem nb070_wpp_notmem_0163 (x : Var) : (nb070_alpha_dummy_011 x) ∉ ((syn_cen)).fv := by
  simpa only [nb070_alpha_dummy_011, fv_syn_cen] using (nb070_compact_fv_empty_0015 x)

theorem nb070_wpp_notmem_0164 (A : Class) : (nb070_alpha_dummy_008 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_008, fv_syn_cen] using (nb070_compact_fv_empty_0016 A)

theorem nb070_wpp_notmem_0165 (x : Var) : (nb070_alpha_dummy_010 x) ∉ ((syn_cen)).fv := by
  simpa only [nb070_alpha_dummy_010, fv_syn_cen] using (nb070_compact_fv_empty_0017 x)

theorem nb070_wpp_notmem_0166 (A : Class) : (nb070_alpha_dummy_001 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_001, fv_syn_cen] using (nb070_compact_fv_empty_0018 A)

theorem nb070_wpp_notmem_0167 (x : Var) : x ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb070_compact_fv_empty_0019 x)

theorem nb070_wpp_notmem_0168 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_000, fv_syn_cen] using (nb070_compact_fv_empty_0000 A)

theorem nb070_wpp_notmem_0169 (b : Var) : b ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb070_compact_fv_empty_0001 b)

theorem nb070_wpp_notmem_0170 (A : Class) : (nb070_alpha_dummy_002 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_002, fv_syn_cen] using (nb070_compact_fv_empty_0002 A)

theorem nb070_wpp_notmem_0171 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_003 x A b) ∉ ((syn_cen)).fv := by
  simpa only [nb070_alpha_dummy_003, fv_syn_cen] using (nb070_compact_fv_empty_0003 x A b)

theorem nb070_wpp_notmem_0172 (A : Class) : (nb070_alpha_dummy_005 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_005, fv_syn_cen] using (nb070_compact_fv_empty_0004 A)

theorem nb070_wpp_notmem_0173 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_007 x A b) ∉ ((syn_cen)).fv := by
  simpa only [nb070_alpha_dummy_007, fv_syn_cen] using (nb070_compact_fv_empty_0005 x A b)

theorem nb070_wpp_notmem_0174 (A : Class) : (nb070_alpha_dummy_004 A) ∉ ((syn_cen)).fv :=
  by simpa only [nb070_alpha_dummy_004, fv_syn_cen] using (nb070_compact_fv_empty_0006 A)

theorem nb070_wpp_notmem_0175 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_006 x A b) ∉ ((syn_cen)).fv := by
  simpa only [nb070_alpha_dummy_006, fv_syn_cen] using (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0010 (x : Var) (A : Class) (b : Var) :
    TEnvFresh
      [((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      ((syn_cen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x)
      (nb070_wpp_notmem_0162 A) (nb070_wpp_notmem_0163 x)
      (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x)
        (nb070_wpp_notmem_0164 A) (nb070_wpp_notmem_0165 x)
        (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0166 A)
          (nb070_wpp_notmem_0167 x)
          (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0168 A)
            (nb070_wpp_notmem_0169 b)
            (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b)
              (nb070_wpp_notmem_0170 A) (nb070_wpp_notmem_0171 x A b)
              (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b)
                (nb070_wpp_notmem_0172 A) (nb070_wpp_notmem_0173 x A b)
                (TEnvFresh.consFresh (nb070_alpha_dummy_004 A)
                  (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0174 A)
                  (nb070_wpp_notmem_0175 x A b) (TEnvFresh.nil ((syn_cen)).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
