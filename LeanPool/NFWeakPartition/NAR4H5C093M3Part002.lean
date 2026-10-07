/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C093M3Part002Block001


/-! NF weak partition development: NAR4H5C093M3Part002. -/


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

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0000`. -/
@[expose]
noncomputable def nb093SplitAlpha0000 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)),
        ((nb093AlphaDummy038 A), (nb093AlphaDummy039 r d)),
        ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy009 A))
          (Class.cv (nb093AlphaDummy000 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
            (synCun (synCphi (Class.cv (nb093AlphaDummy009 A))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy011 r d)) (Class.cv d)) (Wff.neg
          (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
            (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy009 A) from (by
              unfold nb093AlphaDummy009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1))))
          (show d ≠ (nb093AlphaDummy011 r d) from (by
              unfold nb093AlphaDummy011;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1))))
          (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy008 A) from (by
                unfold nb093AlphaDummy008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0))))
            (show d ≠ (nb093AlphaDummy010 r d) from (by
                unfold nb093AlphaDummy010;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0))))
            (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy038 A) from
                (by
                  unfold nb093AlphaDummy038;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0036 A) 0))))
              (show d ≠ (nb093AlphaDummy039 r d) from (by
                  unfold nb093AlphaDummy039;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0037 r d) 0))))
              (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy012 A) from
                  (by
                    unfold nb093AlphaDummy012;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0033 A) 0))))
                (show d ≠ (nb093AlphaDummy013 r d) from (by
                    unfold nb093AlphaDummy013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0035 r d) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy001 A))).fv ∪
                ((Class.cv (nb093AlphaDummy000 A))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy016 A) from
                                      (by
                                        unfold nb093AlphaDummy016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                0)))) (show (nb093AlphaDummy011 r d) ≠
                                        (nb093AlphaDummy018 r d) from (by
                                        unfold nb093AlphaDummy018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 0))))
                                    (TAlphaVar.there (show (nb093AlphaDummy009 A) ≠
        (nb093AlphaDummy017 A) from (by
                                          unfold nb093AlphaDummy017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0010 A) 1)))) (show
                                        (nb093AlphaDummy011 r d) ≠
        (nb093AlphaDummy019 r d) from (by
                                          unfold nb093AlphaDummy019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0011 r d) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy009 A) ≠
        (nb093AlphaDummy042 A) from (by
          unfold nb093AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0040 A) 0)))) (show (nb093AlphaDummy011 r d) ≠
        (nb093AlphaDummy043 r d) from (by
          unfold nb093AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0041 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy040 A) from (by
          unfold nb093AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0038 A) 0)))) (show (nb093AlphaDummy011 r d) ≠
        (nb093AlphaDummy041 r d) from (by
          unfold nb093AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0039 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy009 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy011 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy023 A) from (by
          unfold nb093AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  1)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy026 r d) from (by
          unfold nb093AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy022 A) from (by
          unfold nb093AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy025 r d) from (by
          unfold nb093AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold
            nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy021 r d) from (by
          unfold
            nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018
        r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023
        A) ≠ (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy016 A) from
                                      (by
                                        unfold nb093AlphaDummy016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                0)))) (show (nb093AlphaDummy011 r d) ≠
                                        (nb093AlphaDummy018 r d) from (by
                                        unfold nb093AlphaDummy018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 0))))
                                    (TAlphaVar.there (show (nb093AlphaDummy009 A) ≠
        (nb093AlphaDummy017 A) from (by
                                          unfold nb093AlphaDummy017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0010 A) 1)))) (show
                                        (nb093AlphaDummy011 r d) ≠
        (nb093AlphaDummy019 r d) from (by
                                          unfold nb093AlphaDummy019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0011 r d) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy009 A) ≠
        (nb093AlphaDummy042 A) from (by
          unfold nb093AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0040 A) 0)))) (show (nb093AlphaDummy011 r d) ≠
        (nb093AlphaDummy043 r d) from (by
          unfold nb093AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0041 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy040 A) from (by
          unfold nb093AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0038 A) 0)))) (show (nb093AlphaDummy011 r d) ≠
        (nb093AlphaDummy041 r d) from (by
          unfold nb093AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0039 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy009 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy011 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy023 A) from (by
          unfold nb093AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  1)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy026 r d) from (by
          unfold nb093AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy022 A) from (by
          unfold nb093AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy025 r d) from (by
          unfold nb093AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold
            nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy021 r d) from (by
          unfold
            nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018
        r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023
        A) ≠ (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy042 A), (nb093AlphaDummy043 r d)), ((nb093AlphaDummy040 A),
        (nb093AlphaDummy041 r d)), ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
        ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)), ((nb093AlphaDummy038 A),
        (nb093AlphaDummy039 r d)), ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb093AlphaDummy040 A), (nb093AlphaDummy041 r d)),
                    ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)),
                    ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)),
                    ((nb093AlphaDummy038 A), (nb093AlphaDummy039 r d)),
                    ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
                    ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                    ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                    ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0001`. -/
@[expose]
noncomputable def nb093SplitAlpha0001 (A : Class) (r : Var) (d : Var)
    (dv_d_r : d ≠ r) :
    TAlphaWff
      [((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy012 A)) (synCcompl
            (Class.cab (nb093AlphaDummy008 A)
              (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                  (synCphi (Class.cv (nb093AlphaDummy009 A)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy012 A)) (synCcompl
              (Class.cab (nb093AlphaDummy008 A)
                (synWrex (nb093AlphaDummy009 A) (Class.cv (nb093AlphaDummy000 A))
                  (Wff.classEq (Class.cv (nb093AlphaDummy008 A))
                    (synCun (synCphi (Class.cv (nb093AlphaDummy009 A)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy013 r d)) (synCcompl
            (Class.cab (nb093AlphaDummy010 r d)
              (synWrex (nb093AlphaDummy011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                  (synCphi (Class.cv (nb093AlphaDummy011 r d)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy013 r d)) (synCcompl
              (Class.cab (nb093AlphaDummy010 r d)
                (synWrex (nb093AlphaDummy011 r d) (Class.cv d)
                  (Wff.classEq (Class.cv (nb093AlphaDummy010 r d))
                    (synCun (synCphi (Class.cv (nb093AlphaDummy011 r d)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy009 A) from (by
                              unfold nb093AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
                          (show r ≠ (nb093AlphaDummy011 r d) from (by
                              unfold nb093AlphaDummy011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy008 A) from (by
                                unfold nb093AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
                            (show r ≠ (nb093AlphaDummy010 r d) from (by
                                unfold nb093AlphaDummy010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy014 A) from
                                (by
                                  unfold nb093AlphaDummy014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0008 A) 0))))
                              (show r ≠ (nb093AlphaDummy015 r d) from (by
                                  unfold nb093AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0009 r d)
                                          0)))) (TAlphaVar.there (show
                                  (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy012 A) from (by
                                    unfold nb093AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0005 A)
                                            0)))) (show r ≠ (nb093AlphaDummy013 r d) from (by
                                    unfold nb093AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0007 r d)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb093AlphaDummy001 A))).fv ∪
                              ((Class.cv (nb093AlphaDummy000 A))).fv) (by decide))
                          (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy016 A) from
                                    (by
                                      unfold nb093AlphaDummy016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0010 A)
                                              0)))) (show (nb093AlphaDummy011 r d) ≠
                                      (nb093AlphaDummy018 r d) from (by
                                      unfold nb093AlphaDummy018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0011 r d)
                                              0)))) (TAlphaVar.there (show
                                      (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy017 A) from
                                      (by
                                        unfold nb093AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                1)))) (show (nb093AlphaDummy011 r d) ≠
                                        (nb093AlphaDummy019 r d) from (by
                                        unfold nb093AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb093AlphaDummy009 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb093AlphaDummy011 r d))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy023 A) from (by
          unfold nb093AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014 A)
                  1)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy026 r d) from (by
          unfold nb093AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015 r
                    d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy022 A) from (by
          unfold nb093AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy025 r d) from (by
          unfold nb093AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A),
        (nb093AlphaDummy010 r d)), ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)),
        ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A),
        (nb093AlphaDummy010 r d)), ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)),
        ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r
        d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023
        A) ≠ (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb093AlphaDummy020 A),
        (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A), (nb093AlphaDummy018 r d)),
        ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)), ((nb093AlphaDummy009 A),
        (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)),
        ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)), ((nb093AlphaDummy012 A),
        (nb093AlphaDummy013 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb093AlphaDummy020 A),
        (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A), (nb093AlphaDummy018 r d)),
        ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)), ((nb093AlphaDummy009 A),
        (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)),
        ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)), ((nb093AlphaDummy012 A),
        (nb093AlphaDummy013 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy009 A) from (by
                              unfold nb093AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
                          (show r ≠ (nb093AlphaDummy011 r d) from (by
                              unfold nb093AlphaDummy011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy008 A) from (by
                                unfold nb093AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
                            (show r ≠ (nb093AlphaDummy010 r d) from (by
                                unfold nb093AlphaDummy010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy014 A) from
                                (by
                                  unfold nb093AlphaDummy014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0008 A) 0))))
                              (show r ≠ (nb093AlphaDummy015 r d) from (by
                                  unfold nb093AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0009 r d)
                                          0)))) (TAlphaVar.there (show
                                  (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy012 A) from (by
                                    unfold nb093AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0005 A)
                                            0)))) (show r ≠ (nb093AlphaDummy013 r d) from (by
                                    unfold nb093AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0007 r d)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb093AlphaDummy001 A))).fv ∪
                              ((Class.cv (nb093AlphaDummy000 A))).fv) (by decide))
                          (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy016 A) from
                                    (by
                                      unfold nb093AlphaDummy016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0010 A)
                                              0)))) (show (nb093AlphaDummy011 r d) ≠
                                      (nb093AlphaDummy018 r d) from (by
                                      unfold nb093AlphaDummy018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0011 r d)
                                              0)))) (TAlphaVar.there (show
                                      (nb093AlphaDummy009 A) ≠ (nb093AlphaDummy017 A) from
                                      (by
                                        unfold nb093AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                1)))) (show (nb093AlphaDummy011 r d) ≠
                                        (nb093AlphaDummy019 r d) from (by
                                        unfold nb093AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb093AlphaDummy009 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb093AlphaDummy011 r d))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy023 A) from (by
          unfold nb093AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014 A)
                  1)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy026 r d) from (by
          unfold nb093AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015 r
                    d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy022 A) from (by
          unfold nb093AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy025 r d) from (by
          unfold nb093AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093AlphaDummy018 r d) ≠ (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A),
        (nb093AlphaDummy010 r d)), ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)),
        ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy030 A) from (by
          unfold
            nb093AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy031 r d) from (by
          unfold
            nb093AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy028 A) from (by
          unfold
            nb093AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy029 r d) from (by
          unfold
            nb093AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy024 A), (nb093AlphaDummy027 r d)), ((nb093AlphaDummy023 A),
        (nb093AlphaDummy026 r d)), ((nb093AlphaDummy022 A), (nb093AlphaDummy025 r d)),
        ((nb093AlphaDummy020 A), (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A),
        (nb093AlphaDummy018 r d)), ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)),
        ((nb093AlphaDummy009 A), (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A),
        (nb093AlphaDummy010 r d)), ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)),
        ((nb093AlphaDummy012 A), (nb093AlphaDummy013 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r
        d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy016 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy018 r d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy023
        A) ≠ (nb093AlphaDummy034 A) from (by
          unfold
            nb093AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy035 r d) from (by
          unfold
            nb093AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy023 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093AlphaDummy026 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy016
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy018 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy024
        A) ≠ (nb093AlphaDummy036 A) from (by
          unfold
            nb093AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy037 r d) from (by
          unfold
            nb093AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy024 A) ≠
        (nb093AlphaDummy032 A) from (by
          unfold
            nb093AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093AlphaDummy027 r d) ≠ (nb093AlphaDummy033 r d) from (by
          unfold
            nb093AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb093AlphaDummy020 A),
        (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A), (nb093AlphaDummy018 r d)),
        ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)), ((nb093AlphaDummy009 A),
        (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)),
        ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)), ((nb093AlphaDummy012 A),
        (nb093AlphaDummy013 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb093AlphaDummy016 A) ≠
        (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy016 A) ≠ (nb093AlphaDummy020 A) from (by
          unfold nb093AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093AlphaDummy018 r d) ≠
        (nb093AlphaDummy021 r d) from (by
          unfold nb093AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb093AlphaDummy020 A),
        (nb093AlphaDummy021 r d)), ((nb093AlphaDummy016 A), (nb093AlphaDummy018 r d)),
        ((nb093AlphaDummy017 A), (nb093AlphaDummy019 r d)), ((nb093AlphaDummy009 A),
        (nb093AlphaDummy011 r d)), ((nb093AlphaDummy008 A), (nb093AlphaDummy010 r d)),
        ((nb093AlphaDummy014 A), (nb093AlphaDummy015 r d)), ((nb093AlphaDummy012 A),
        (nb093AlphaDummy013 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb093SplitAlpha0000 A r d)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb093SplitAlpha0000 A r d)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
