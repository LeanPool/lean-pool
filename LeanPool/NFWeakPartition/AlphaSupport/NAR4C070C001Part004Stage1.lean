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

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0004`. -/
@[expose]
noncomputable def nb070SplitAlpha0004 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
        ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
        ((nb070AlphaDummy058 A), (nb070AlphaDummy059 x)),
        ((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
        ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
        ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
        ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
        ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.imp (Wff.classMem (Class.cv (nb070AlphaDummy032 A))
          (Class.cv (nb070AlphaDummy025 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb070AlphaDummy033 A))
            (synCif (Wff.classMem (Class.cv (nb070AlphaDummy032 A)) (synCnnc))
              (synCplc (Class.cv (nb070AlphaDummy032 A)) (synC1c))
              (Class.cv (nb070AlphaDummy032 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb070AlphaDummy034 x))
          (Class.cv (nb070AlphaDummy027 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb070AlphaDummy035 x))
            (synCif (Wff.classMem (Class.cv (nb070AlphaDummy034 x)) (synCnnc))
              (synCplc (Class.cv (nb070AlphaDummy034 x)) (synC1c))
              (Class.cv (nb070AlphaDummy034 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb070AlphaDummy025 A) ≠ (nb070AlphaDummy032 A) from (by
              unfold nb070AlphaDummy032;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 0))))
          (show (nb070AlphaDummy027 x) ≠ (nb070AlphaDummy034 x) from (by
              unfold nb070AlphaDummy034;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 0))))
          (TAlphaVar.there (show (nb070AlphaDummy025 A) ≠ (nb070AlphaDummy033 A) from (by
                unfold nb070AlphaDummy033;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 1))))
            (show (nb070AlphaDummy027 x) ≠ (nb070AlphaDummy035 x) from (by
                unfold nb070AlphaDummy035;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 1))))
            (TAlphaVar.there (show (nb070AlphaDummy025 A) ≠ (nb070AlphaDummy058 A) from
                (by
                  unfold nb070AlphaDummy058;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0054 A) 0))))
              (show (nb070AlphaDummy027 x) ≠ (nb070AlphaDummy059 x) from (by
                  unfold nb070AlphaDummy059;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0055 x) 0))))
              (TAlphaVar.there (show (nb070AlphaDummy025 A) ≠ (nb070AlphaDummy056 A) from
                  (by
                    unfold nb070AlphaDummy056;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0052 A) 0))))
                (show (nb070AlphaDummy027 x) ≠ (nb070AlphaDummy057 x) from (by
                    unfold nb070AlphaDummy057;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0053 x) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb070AlphaDummy025 A))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb070AlphaDummy027 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy039 A) from
                                (by
                                  unfold nb070AlphaDummy039;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0028 A) 1))))
                              (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy042 x) from
                                (by
                                  unfold nb070AlphaDummy042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0029 x) 1))))
                              (TAlphaVar.there (show
                                  (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy038 A) from (by
                                    unfold nb070AlphaDummy038;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb070_support_mem_0028 A)
                                            0)))) (show
                                  (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy041 x) from (by
                                    unfold nb070AlphaDummy041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb070_support_mem_0029 x)
                                            0)))) (TAlphaVar.there (show
                                    (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from
                                    (by
                                      unfold nb070AlphaDummy036;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0026 A)
                                              0)))) (show
                                    (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from
                                    (by
                                      unfold nb070AlphaDummy037;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0027 x)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb070AlphaDummy040 A), (nb070AlphaDummy043 x)),
                                  ((nb070AlphaDummy039 A), (nb070AlphaDummy042 x)),
                                  ((nb070AlphaDummy038 A), (nb070AlphaDummy041 x)),
                                  ((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
                                  ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
                                  ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
                                  ((nb070AlphaDummy058 A), (nb070AlphaDummy059 x)),
                                  ((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
                                  ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                                  ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                                  ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
                                  ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                                  ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                                  ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                                  ((nb070AlphaDummy001 A), x),
                                  ((nb070AlphaDummy000 A), b), ((nb070AlphaDummy002 A),
                                    (nb070AlphaDummy003 x A b)), ((nb070AlphaDummy005 A),
                                    (nb070AlphaDummy007 x A b)), ((nb070AlphaDummy004 A),
                                    (nb070AlphaDummy006 x A b))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb070SplitAlpha0003 x A b))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from (by
                          unfold nb070AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                      (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from (by
                          unfold nb070AlphaDummy037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
                      ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
                      ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
                      ((nb070AlphaDummy058 A), (nb070AlphaDummy059 x)),
                      ((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
                      ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                      ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                      ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
                      ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                      ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                      ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                      ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                      ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                      ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                      ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from (by
                        unfold nb070AlphaDummy036;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                    (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from (by
                        unfold nb070AlphaDummy037;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb070AlphaDummy032 A) ≠ (nb070AlphaDummy036 A) from (by
                          unfold nb070AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                      (show (nb070AlphaDummy034 x) ≠ (nb070AlphaDummy037 x) from (by
                          unfold nb070AlphaDummy037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb070AlphaDummy036 A), (nb070AlphaDummy037 x)),
                      ((nb070AlphaDummy032 A), (nb070AlphaDummy034 x)),
                      ((nb070AlphaDummy033 A), (nb070AlphaDummy035 x)),
                      ((nb070AlphaDummy058 A), (nb070AlphaDummy059 x)),
                      ((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
                      ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                      ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                      ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
                      ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                      ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                      ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                      ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                      ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                      ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                      ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0005`. -/
@[expose]
noncomputable def nb070SplitAlpha0005 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
        ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
        ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.imp (Wff.classMem (Class.cv (nb070AlphaDummy054 A))
          (Class.cab (nb070AlphaDummy024 A)
            (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
              (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb070AlphaDummy054 A))
            (Class.cab (nb070AlphaDummy024 A)
              (synWrex (nb070AlphaDummy025 A) (Class.cv (nb070AlphaDummy008 A))
                (Wff.classEq (Class.cv (nb070AlphaDummy024 A))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy025 A)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb070AlphaDummy055 x))
          (Class.cab (nb070AlphaDummy026 x)
            (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
              (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb070AlphaDummy055 x))
            (Class.cab (nb070AlphaDummy026 x)
              (synWrex (nb070AlphaDummy027 x) (Class.cv (nb070AlphaDummy010 x))
                (Wff.classEq (Class.cv (nb070AlphaDummy026 x))
                  (synCun (synCphi (Class.cv (nb070AlphaDummy027 x)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy025 A) from (by
                      unfold nb070AlphaDummy025;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 1))))
                  (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy027 x) from (by
                      unfold nb070AlphaDummy027;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 1))))
                  (TAlphaVar.there
                    (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy024 A) from (by
                        unfold nb070AlphaDummy024;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0046 A) 0))))
                    (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy026 x) from (by
                        unfold nb070AlphaDummy026;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0048 x) 0)))) (TAlphaVar.there
                      (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy054 A) from (by
                          unfold nb070AlphaDummy054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0050 A) 0))))
                      (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy055 x) from (by
                          unfold nb070AlphaDummy055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0051 x) 0))))
                      (TAlphaVar.there
                        (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy028 A) from (by
                            unfold nb070AlphaDummy028;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0047 A) 0))))
                        (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy029 x) from (by
                            unfold nb070AlphaDummy029;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0049 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCen)).fv ∪ ((synCsn
                                  (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv)
                            (by decide)) (freshVar_injective
                            (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb070AlphaDummy009 A))).fv ∪
                      ((Class.cv (nb070AlphaDummy008 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb070AlphaDummy011 x))).fv ∪
                      ((Class.cv (nb070AlphaDummy010 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb070SplitAlpha0004 x A b)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb070SplitAlpha0004 x A b)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
                          ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                          ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                          ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
                          ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                          ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                          ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                          ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                          ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                          ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                          ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy025 A) from (by
                        unfold nb070AlphaDummy025;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0046 A) 1))))
                    (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy027 x) from (by
                        unfold nb070AlphaDummy027;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0048 x) 1)))) (TAlphaVar.there
                      (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy024 A) from (by
                          unfold nb070AlphaDummy024;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0046 A) 0))))
                      (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy026 x) from (by
                          unfold nb070AlphaDummy026;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb070_support_mem_0048 x) 0))))
                      (TAlphaVar.there
                        (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy054 A) from (by
                            unfold nb070AlphaDummy054;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0050 A) 0))))
                        (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy055 x) from (by
                            unfold nb070AlphaDummy055;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0051 x) 0))))
                        (TAlphaVar.there
                          (show (nb070AlphaDummy008 A) ≠ (nb070AlphaDummy028 A) from (by
                              unfold nb070AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0047 A) 0))))
                          (show (nb070AlphaDummy010 x) ≠ (nb070AlphaDummy029 x) from (by
                              unfold nb070AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0049 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCen)).fv ∪ ((synCsn
                                    (synCpw1 (Class.cv (nb070AlphaDummy001 A))))).fv)
                              (by decide)) (freshVar_injective
                              (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv x)))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb070AlphaDummy009 A))).fv ∪
                        ((Class.cv (nb070AlphaDummy008 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb070AlphaDummy011 x))).fv ∪
                        ((Class.cv (nb070AlphaDummy010 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb070SplitAlpha0004 x A b)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb070SplitAlpha0004 x A b)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb070AlphaDummy056 A), (nb070AlphaDummy057 x)),
                            ((nb070AlphaDummy025 A), (nb070AlphaDummy027 x)),
                            ((nb070AlphaDummy024 A), (nb070AlphaDummy026 x)),
                            ((nb070AlphaDummy054 A), (nb070AlphaDummy055 x)),
                            ((nb070AlphaDummy028 A), (nb070AlphaDummy029 x)),
                            ((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                            ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                            ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                            ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                            ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                            ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb070_wpp_notmem_0162 (A : Class) : (nb070AlphaDummy009 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy009, fv_syn_cen] using (nb070_compact_fv_empty_0014 A)

theorem nb070_wpp_notmem_0163 (x : Var) : (nb070AlphaDummy011 x) ∉ ((synCen)).fv := by
  simpa only [nb070AlphaDummy011, fv_syn_cen] using (nb070_compact_fv_empty_0015 x)

theorem nb070_wpp_notmem_0164 (A : Class) : (nb070AlphaDummy008 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy008, fv_syn_cen] using (nb070_compact_fv_empty_0016 A)

theorem nb070_wpp_notmem_0165 (x : Var) : (nb070AlphaDummy010 x) ∉ ((synCen)).fv := by
  simpa only [nb070AlphaDummy010, fv_syn_cen] using (nb070_compact_fv_empty_0017 x)

theorem nb070_wpp_notmem_0166 (A : Class) : (nb070AlphaDummy001 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy001, fv_syn_cen] using (nb070_compact_fv_empty_0018 A)

theorem nb070_wpp_notmem_0167 (x : Var) : x ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb070_compact_fv_empty_0019 x)

theorem nb070_wpp_notmem_0168 (A : Class) : (nb070AlphaDummy000 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy000, fv_syn_cen] using (nb070_compact_fv_empty_0000 A)

theorem nb070_wpp_notmem_0169 (b : Var) : b ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb070_compact_fv_empty_0001 b)

theorem nb070_wpp_notmem_0170 (A : Class) : (nb070AlphaDummy002 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy002, fv_syn_cen] using (nb070_compact_fv_empty_0002 A)

theorem nb070_wpp_notmem_0171 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy003 x A b) ∉ ((synCen)).fv := by
  simpa only [nb070AlphaDummy003, fv_syn_cen] using (nb070_compact_fv_empty_0003 x A b)

theorem nb070_wpp_notmem_0172 (A : Class) : (nb070AlphaDummy005 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy005, fv_syn_cen] using (nb070_compact_fv_empty_0004 A)

theorem nb070_wpp_notmem_0173 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy007 x A b) ∉ ((synCen)).fv := by
  simpa only [nb070AlphaDummy007, fv_syn_cen] using (nb070_compact_fv_empty_0005 x A b)

theorem nb070_wpp_notmem_0174 (A : Class) : (nb070AlphaDummy004 A) ∉ ((synCen)).fv :=
  by simpa only [nb070AlphaDummy004, fv_syn_cen] using (nb070_compact_fv_empty_0006 A)

theorem nb070_wpp_notmem_0175 (x : Var) (A : Class) (b : Var) :
    (nb070AlphaDummy006 x A b) ∉ ((synCen)).fv := by
  simpa only [nb070AlphaDummy006, fv_syn_cen] using (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0010 (x : Var) (A : Class) (b : Var) :
    TEnvFresh
      [((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      ((synCen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb070AlphaDummy009 A) (nb070AlphaDummy011 x)
      (nb070_wpp_notmem_0162 A) (nb070_wpp_notmem_0163 x)
      (TEnvFresh.consFresh (nb070AlphaDummy008 A) (nb070AlphaDummy010 x)
        (nb070_wpp_notmem_0164 A) (nb070_wpp_notmem_0165 x)
        (TEnvFresh.consFresh (nb070AlphaDummy001 A) x (nb070_wpp_notmem_0166 A)
          (nb070_wpp_notmem_0167 x)
          (TEnvFresh.consFresh (nb070AlphaDummy000 A) b (nb070_wpp_notmem_0168 A)
            (nb070_wpp_notmem_0169 b)
            (TEnvFresh.consFresh (nb070AlphaDummy002 A) (nb070AlphaDummy003 x A b)
              (nb070_wpp_notmem_0170 A) (nb070_wpp_notmem_0171 x A b)
              (TEnvFresh.consFresh (nb070AlphaDummy005 A) (nb070AlphaDummy007 x A b)
                (nb070_wpp_notmem_0172 A) (nb070_wpp_notmem_0173 x A b)
                (TEnvFresh.consFresh (nb070AlphaDummy004 A)
                  (nb070AlphaDummy006 x A b) (nb070_wpp_notmem_0174 A)
                  (nb070_wpp_notmem_0175 x A b) (TEnvFresh.nil ((synCen)).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
