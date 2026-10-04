/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part008

/-! NF weak partition development: NAR4H5C095M3Part009. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0001`. -/
@[expose]
noncomputable def nb095SplitAlpha0001 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy051 D R S_cls E), (nb095AlphaDummy052 f)),
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy049 D R S_cls E), (nb095AlphaDummy050 f)),
        ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy051 D R S_cls E))
          (synCcompl (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy051 D R S_cls E))
            (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy052 f))
          (synCcompl (synCphi (Class.cv (nb095AlphaDummy022 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy052 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                              (nb095AlphaDummy027 D R S_cls E) from (by
                              unfold nb095AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0010 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy029 f) from (by
                              unfold nb095AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0011 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                                (nb095AlphaDummy028 D R S_cls E) from (by
                                unfold nb095AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0010 D R S_cls E) 1))))
                            (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy030 f) from (by
                                unfold nb095AlphaDummy030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0011 f) 1))))
                            (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                                  (nb095AlphaDummy053 D R S_cls E) from (by
                                  unfold nb095AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0040 D R S_cls E) 0))))
                              (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy054 f) from
                                (by
                                  unfold nb095AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0041 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                                    (nb095AlphaDummy051 D R S_cls E) from (by
                                    unfold nb095AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0038 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy052 f) from (by
                                    unfold nb095AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0039 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy022 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy027 D R S_cls E) ≠
        (nb095AlphaDummy034 D R S_cls E) from (by
          unfold nb095AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy037 f) from (by
          unfold nb095AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy027 D R S_cls E) ≠ (nb095AlphaDummy033 D R S_cls E) from (by
          unfold nb095AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy036 f) from (by
          unfold nb095AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy027 D R S_cls E) ≠ (nb095AlphaDummy031 D R S_cls E) from (by
          unfold nb095AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0012 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from (by
          unfold nb095AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy035 D R S_cls E), (nb095AlphaDummy038 f)),
        ((nb095AlphaDummy034 D R S_cls E), (nb095AlphaDummy037 f)),
        ((nb095AlphaDummy033 D R S_cls E), (nb095AlphaDummy036 f)),
        ((nb095AlphaDummy031 D R S_cls E), (nb095AlphaDummy032 f)),
        ((nb095AlphaDummy027 D R S_cls E), (nb095AlphaDummy029 f)),
        ((nb095AlphaDummy028 D R S_cls E), (nb095AlphaDummy030 f)),
        ((nb095AlphaDummy053 D R S_cls E), (nb095AlphaDummy054 f)),
        ((nb095AlphaDummy051 D R S_cls E), (nb095AlphaDummy052 f)),
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy049 D R S_cls E), (nb095AlphaDummy050 f)),
        ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy034
        D R S_cls E) ≠ (nb095AlphaDummy041 D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy035 D R S_cls E), (nb095AlphaDummy038 f)),
        ((nb095AlphaDummy034 D R S_cls E), (nb095AlphaDummy037 f)),
        ((nb095AlphaDummy033 D R S_cls E), (nb095AlphaDummy036 f)),
        ((nb095AlphaDummy031 D R S_cls E), (nb095AlphaDummy032 f)),
        ((nb095AlphaDummy027 D R S_cls E), (nb095AlphaDummy029 f)),
        ((nb095AlphaDummy028 D R S_cls E), (nb095AlphaDummy030 f)),
        ((nb095AlphaDummy053 D R S_cls E), (nb095AlphaDummy054 f)),
        ((nb095AlphaDummy051 D R S_cls E), (nb095AlphaDummy052 f)),
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy049 D R S_cls E), (nb095AlphaDummy050 f)),
        ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy045
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy046 f) from (by
          unfold
            nb095AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy045
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy046 f) from (by
          unfold
            nb095AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy035
        D R S_cls E) ≠ (nb095AlphaDummy047 D R S_cls E) from (by
          unfold
            nb095AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy048 f) from (by
          unfold
            nb095AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy035
        D R S_cls E) ≠ (nb095AlphaDummy047 D R S_cls E) from (by
          unfold
            nb095AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy048 f) from (by
          unfold
            nb095AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy027 D R S_cls E) ≠
                                        (nb095AlphaDummy031 D R S_cls E) from (by
                                        unfold nb095AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from
                                      (by
                                        unfold nb095AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy031 D R S_cls E),
                                      (nb095AlphaDummy032 f)),
                                    ((nb095AlphaDummy027 D R S_cls E),
                                      (nb095AlphaDummy029 f)),
                                    ((nb095AlphaDummy028 D R S_cls E),
                                      (nb095AlphaDummy030 f)),
                                    ((nb095AlphaDummy053 D R S_cls E),
                                      (nb095AlphaDummy054 f)),
                                    ((nb095AlphaDummy051 D R S_cls E),
                                      (nb095AlphaDummy052 f)),
                                    ((nb095AlphaDummy020 D R S_cls E),
                                      (nb095AlphaDummy022 f)),
                                    ((nb095AlphaDummy019 D R S_cls E),
                                      (nb095AlphaDummy021 f)),
                                    ((nb095AlphaDummy049 D R S_cls E),
                                      (nb095AlphaDummy050 f)),
                                    ((nb095AlphaDummy023 D R S_cls E),
                                      (nb095AlphaDummy024 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy027 D R S_cls E) ≠
                                      (nb095AlphaDummy031 D R S_cls E) from (by
                                      unfold nb095AlphaDummy031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from
                                    (by
                                      unfold nb095AlphaDummy032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy027 D R S_cls E) ≠
                                        (nb095AlphaDummy031 D R S_cls E) from (by
                                        unfold nb095AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from
                                      (by
                                        unfold nb095AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy031 D R S_cls E),
                                      (nb095AlphaDummy032 f)),
                                    ((nb095AlphaDummy027 D R S_cls E),
                                      (nb095AlphaDummy029 f)),
                                    ((nb095AlphaDummy028 D R S_cls E),
                                      (nb095AlphaDummy030 f)),
                                    ((nb095AlphaDummy053 D R S_cls E),
                                      (nb095AlphaDummy054 f)),
                                    ((nb095AlphaDummy051 D R S_cls E),
                                      (nb095AlphaDummy052 f)),
                                    ((nb095AlphaDummy020 D R S_cls E),
                                      (nb095AlphaDummy022 f)),
                                    ((nb095AlphaDummy019 D R S_cls E),
                                      (nb095AlphaDummy021 f)),
                                    ((nb095AlphaDummy049 D R S_cls E),
                                      (nb095AlphaDummy050 f)),
                                    ((nb095AlphaDummy023 D R S_cls E),
                                      (nb095AlphaDummy024 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                              (nb095AlphaDummy027 D R S_cls E) from (by
                              unfold nb095AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0010 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy029 f) from (by
                              unfold nb095AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0011 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                                (nb095AlphaDummy028 D R S_cls E) from (by
                                unfold nb095AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0010 D R S_cls E) 1))))
                            (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy030 f) from (by
                                unfold nb095AlphaDummy030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0011 f) 1))))
                            (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                                  (nb095AlphaDummy053 D R S_cls E) from (by
                                  unfold nb095AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0040 D R S_cls E) 0))))
                              (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy054 f) from
                                (by
                                  unfold nb095AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0041 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy020 D R S_cls E) ≠
                                    (nb095AlphaDummy051 D R S_cls E) from (by
                                    unfold nb095AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0038 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy052 f) from (by
                                    unfold nb095AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0039 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy022 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy027 D R S_cls E) ≠
        (nb095AlphaDummy034 D R S_cls E) from (by
          unfold nb095AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy037 f) from (by
          unfold nb095AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy027 D R S_cls E) ≠ (nb095AlphaDummy033 D R S_cls E) from (by
          unfold nb095AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy036 f) from (by
          unfold nb095AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy027 D R S_cls E) ≠ (nb095AlphaDummy031 D R S_cls E) from (by
          unfold nb095AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0012 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from (by
          unfold nb095AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy035 D R S_cls E), (nb095AlphaDummy038 f)),
        ((nb095AlphaDummy034 D R S_cls E), (nb095AlphaDummy037 f)),
        ((nb095AlphaDummy033 D R S_cls E), (nb095AlphaDummy036 f)),
        ((nb095AlphaDummy031 D R S_cls E), (nb095AlphaDummy032 f)),
        ((nb095AlphaDummy027 D R S_cls E), (nb095AlphaDummy029 f)),
        ((nb095AlphaDummy028 D R S_cls E), (nb095AlphaDummy030 f)),
        ((nb095AlphaDummy053 D R S_cls E), (nb095AlphaDummy054 f)),
        ((nb095AlphaDummy051 D R S_cls E), (nb095AlphaDummy052 f)),
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy049 D R S_cls E), (nb095AlphaDummy050 f)),
        ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy034
        D R S_cls E) ≠ (nb095AlphaDummy041 D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy042 f) from (by
          unfold
            nb095AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy039 D R S_cls E) from (by
          unfold
            nb095AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy040 f) from (by
          unfold
            nb095AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy035 D R S_cls E), (nb095AlphaDummy038 f)),
        ((nb095AlphaDummy034 D R S_cls E), (nb095AlphaDummy037 f)),
        ((nb095AlphaDummy033 D R S_cls E), (nb095AlphaDummy036 f)),
        ((nb095AlphaDummy031 D R S_cls E), (nb095AlphaDummy032 f)),
        ((nb095AlphaDummy027 D R S_cls E), (nb095AlphaDummy029 f)),
        ((nb095AlphaDummy028 D R S_cls E), (nb095AlphaDummy030 f)),
        ((nb095AlphaDummy053 D R S_cls E), (nb095AlphaDummy054 f)),
        ((nb095AlphaDummy051 D R S_cls E), (nb095AlphaDummy052 f)),
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy049 D R S_cls E), (nb095AlphaDummy050 f)),
        ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy045
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy046 f) from (by
          unfold
            nb095AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy045
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy046 f) from (by
          unfold
            nb095AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy027
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy035
        D R S_cls E) ≠ (nb095AlphaDummy047 D R S_cls E) from (by
          unfold
            nb095AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy048 f) from (by
          unfold
            nb095AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy035
        D R S_cls E) ≠ (nb095AlphaDummy047 D R S_cls E) from (by
          unfold
            nb095AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy048 f) from (by
          unfold
            nb095AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠
        (nb095AlphaDummy043 D R S_cls E) from (by
          unfold
            nb095AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy038 f) ≠ (nb095AlphaDummy044 f) from (by
          unfold
            nb095AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy027 D R S_cls E) ≠
                                        (nb095AlphaDummy031 D R S_cls E) from (by
                                        unfold nb095AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from
                                      (by
                                        unfold nb095AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy031 D R S_cls E),
                                      (nb095AlphaDummy032 f)),
                                    ((nb095AlphaDummy027 D R S_cls E),
                                      (nb095AlphaDummy029 f)),
                                    ((nb095AlphaDummy028 D R S_cls E),
                                      (nb095AlphaDummy030 f)),
                                    ((nb095AlphaDummy053 D R S_cls E),
                                      (nb095AlphaDummy054 f)),
                                    ((nb095AlphaDummy051 D R S_cls E),
                                      (nb095AlphaDummy052 f)),
                                    ((nb095AlphaDummy020 D R S_cls E),
                                      (nb095AlphaDummy022 f)),
                                    ((nb095AlphaDummy019 D R S_cls E),
                                      (nb095AlphaDummy021 f)),
                                    ((nb095AlphaDummy049 D R S_cls E),
                                      (nb095AlphaDummy050 f)),
                                    ((nb095AlphaDummy023 D R S_cls E),
                                      (nb095AlphaDummy024 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy027 D R S_cls E) ≠
                                      (nb095AlphaDummy031 D R S_cls E) from (by
                                      unfold nb095AlphaDummy031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from
                                    (by
                                      unfold nb095AlphaDummy032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy027 D R S_cls E) ≠
                                        (nb095AlphaDummy031 D R S_cls E) from (by
                                        unfold nb095AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy032 f) from
                                      (by
                                        unfold nb095AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy031 D R S_cls E),
                                      (nb095AlphaDummy032 f)),
                                    ((nb095AlphaDummy027 D R S_cls E),
                                      (nb095AlphaDummy029 f)),
                                    ((nb095AlphaDummy028 D R S_cls E),
                                      (nb095AlphaDummy030 f)),
                                    ((nb095AlphaDummy053 D R S_cls E),
                                      (nb095AlphaDummy054 f)),
                                    ((nb095AlphaDummy051 D R S_cls E),
                                      (nb095AlphaDummy052 f)),
                                    ((nb095AlphaDummy020 D R S_cls E),
                                      (nb095AlphaDummy022 f)),
                                    ((nb095AlphaDummy019 D R S_cls E),
                                      (nb095AlphaDummy021 f)),
                                    ((nb095AlphaDummy049 D R S_cls E),
                                      (nb095AlphaDummy050 f)),
                                    ((nb095AlphaDummy023 D R S_cls E),
                                      (nb095AlphaDummy024 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed
          [((nb095AlphaDummy051 D R S_cls E), (nb095AlphaDummy052 f)),
            ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
            ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
            ((nb095AlphaDummy049 D R S_cls E), (nb095AlphaDummy050 f)),
            ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
            ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
            ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
            ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
            ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
            ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
            ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
            ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0002`. -/
@[expose]
noncomputable def nb095SplitAlpha0002 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy061 D R S_cls E), (nb095AlphaDummy062 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy061 D R S_cls E))
          (Class.cab (nb095AlphaDummy055 D R S_cls E)
            (synWrex (nb095AlphaDummy056 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy061 D R S_cls E))
            (Class.cab (nb095AlphaDummy055 D R S_cls E)
              (synWrex (nb095AlphaDummy056 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy055 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy056 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy062 f))
          (Class.cab (nb095AlphaDummy057 f)
            (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                (synCphi (Class.cv (nb095AlphaDummy058 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy062 f))
            (Class.cab (nb095AlphaDummy057 f)
              (synWrex (nb095AlphaDummy058 f) (Class.cv (nb095AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy057 f))
                  (synCphi (Class.cv (nb095AlphaDummy058 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                      (nb095AlphaDummy056 D R S_cls E) from (by
                      unfold nb095AlphaDummy056;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 1))))
                  (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy058 f) from (by
                      unfold nb095AlphaDummy058;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0044 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                        (nb095AlphaDummy055 D R S_cls E) from (by
                        unfold nb095AlphaDummy055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 0))))
                    (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy057 f) from (by
                        unfold nb095AlphaDummy057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0044 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy011 D R S_cls E) ≠
                          (nb095AlphaDummy061 D R S_cls E) from (by
                          unfold nb095AlphaDummy061;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0046 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy062 f) from (by
                          unfold nb095AlphaDummy062;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0047 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                            (nb095AlphaDummy059 D R S_cls E) from (by
                            unfold nb095AlphaDummy059;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0043 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy060 f) from (by
                            unfold nb095AlphaDummy060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0045 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv
                                  (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv
                                    (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy016 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                              (nb095AlphaDummy063 D R S_cls E) from (by
                              unfold nb095AlphaDummy063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0048 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy065 f) from (by
                              unfold nb095AlphaDummy065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0049 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                                (nb095AlphaDummy064 D R S_cls E) from (by
                                unfold nb095AlphaDummy064;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0048 D R S_cls E) 1))))
                            (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy066 f) from (by
                                unfold nb095AlphaDummy066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0049 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy058 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy063 D R S_cls E) ≠
        (nb095AlphaDummy070 D R S_cls E) from (by
          unfold nb095AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy073 f) from (by
          unfold nb095AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy069 D R S_cls E) from (by
          unfold nb095AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy072 f) from (by
          unfold nb095AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy067 D R S_cls E) from (by
          unfold nb095AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0050 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from (by
          unfold nb095AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy056 D R S_cls E), (nb095AlphaDummy058 f)),
        ((nb095AlphaDummy055 D R S_cls E), (nb095AlphaDummy057 f)),
        ((nb095AlphaDummy061 D R S_cls E), (nb095AlphaDummy062 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy070
        D R S_cls E) ≠ (nb095AlphaDummy077 D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy056 D R S_cls E), (nb095AlphaDummy058 f)),
        ((nb095AlphaDummy055 D R S_cls E), (nb095AlphaDummy057 f)),
        ((nb095AlphaDummy061 D R S_cls E), (nb095AlphaDummy062 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy081
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy081
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071
        D R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071
        D R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy063 D R S_cls E) ≠
                                        (nb095AlphaDummy067 D R S_cls E) from (by
                                        unfold nb095AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                      (by
                                        unfold nb095AlphaDummy068;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy067 D R S_cls E),
                                      (nb095AlphaDummy068 f)),
                                    ((nb095AlphaDummy063 D R S_cls E),
                                      (nb095AlphaDummy065 f)),
                                    ((nb095AlphaDummy064 D R S_cls E),
                                      (nb095AlphaDummy066 f)),
                                    ((nb095AlphaDummy056 D R S_cls E),
                                      (nb095AlphaDummy058 f)),
                                    ((nb095AlphaDummy055 D R S_cls E),
                                      (nb095AlphaDummy057 f)),
                                    ((nb095AlphaDummy061 D R S_cls E),
                                      (nb095AlphaDummy062 f)),
                                    ((nb095AlphaDummy059 D R S_cls E),
                                      (nb095AlphaDummy060 f)),
                                    ((nb095AlphaDummy013 D R S_cls E),
                                      (nb095AlphaDummy016 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy063 D R S_cls E) ≠
                                      (nb095AlphaDummy067 D R S_cls E) from (by
                                      unfold nb095AlphaDummy067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                    (by
                                      unfold nb095AlphaDummy068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy063 D R S_cls E) ≠
                                        (nb095AlphaDummy067 D R S_cls E) from (by
                                        unfold nb095AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                      (by
                                        unfold nb095AlphaDummy068;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy067 D R S_cls E),
                                      (nb095AlphaDummy068 f)),
                                    ((nb095AlphaDummy063 D R S_cls E),
                                      (nb095AlphaDummy065 f)),
                                    ((nb095AlphaDummy064 D R S_cls E),
                                      (nb095AlphaDummy066 f)),
                                    ((nb095AlphaDummy056 D R S_cls E),
                                      (nb095AlphaDummy058 f)),
                                    ((nb095AlphaDummy055 D R S_cls E),
                                      (nb095AlphaDummy057 f)),
                                    ((nb095AlphaDummy061 D R S_cls E),
                                      (nb095AlphaDummy062 f)),
                                    ((nb095AlphaDummy059 D R S_cls E),
                                      (nb095AlphaDummy060 f)),
                                    ((nb095AlphaDummy013 D R S_cls E),
                                      (nb095AlphaDummy016 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy009 D R S_cls E),
                                      (nb095AlphaDummy010 f)),
                                    ((nb095AlphaDummy007 D R S_cls E),
                                      (nb095AlphaDummy008 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                        (nb095AlphaDummy056 D R S_cls E) from (by
                        unfold nb095AlphaDummy056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E) 1))))
                    (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy058 f) from (by
                        unfold nb095AlphaDummy058;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0044 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy011 D R S_cls E) ≠
                          (nb095AlphaDummy055 D R S_cls E) from (by
                          unfold nb095AlphaDummy055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0042 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy057 f) from (by
                          unfold nb095AlphaDummy057;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0044 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                            (nb095AlphaDummy061 D R S_cls E) from (by
                            unfold nb095AlphaDummy061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0046 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy062 f) from (by
                            unfold nb095AlphaDummy062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0047 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                              (nb095AlphaDummy059 D R S_cls E) from (by
                              unfold nb095AlphaDummy059;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0043 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy060 f) from (by
                              unfold nb095AlphaDummy060;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0045 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv
                                    (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
                                  ((synCcnv
                                      (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy016 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy056 D R S_cls E) ≠
                                (nb095AlphaDummy063 D R S_cls E) from (by
                                unfold nb095AlphaDummy063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0048 D R S_cls E) 0))))
                            (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy065 f) from (by
                                unfold nb095AlphaDummy065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0049 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy056 D R S_cls E) ≠
                                  (nb095AlphaDummy064 D R S_cls E) from (by
                                  unfold nb095AlphaDummy064;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0048 D R S_cls E) 1))))
                              (show (nb095AlphaDummy058 f) ≠ (nb095AlphaDummy066 f) from
                                (by
                                  unfold nb095AlphaDummy066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0049 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy058 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy070 D R S_cls E) from (by
          unfold nb095AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy073 f) from (by
          unfold nb095AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy069 D R S_cls E) from (by
          unfold nb095AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0052 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy072 f) from (by
          unfold nb095AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0053 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy063 D R S_cls E) ≠
        (nb095AlphaDummy067 D R S_cls E) from (by
          unfold nb095AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0050 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from (by
          unfold nb095AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy056 D R S_cls E), (nb095AlphaDummy058 f)),
        ((nb095AlphaDummy055 D R S_cls E), (nb095AlphaDummy057 f)),
        ((nb095AlphaDummy061 D R S_cls E), (nb095AlphaDummy062 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy070
        D R S_cls E) ≠ (nb095AlphaDummy077 D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0056
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0054
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠ (nb095AlphaDummy077
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0060
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy078 f) from (by
          unfold
            nb095AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy075 D R S_cls E) from (by
          unfold
            nb095AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0058
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy076 f) from (by
          unfold
            nb095AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy071 D R S_cls E), (nb095AlphaDummy074 f)),
        ((nb095AlphaDummy070 D R S_cls E), (nb095AlphaDummy073 f)),
        ((nb095AlphaDummy069 D R S_cls E), (nb095AlphaDummy072 f)),
        ((nb095AlphaDummy067 D R S_cls E), (nb095AlphaDummy068 f)),
        ((nb095AlphaDummy063 D R S_cls E), (nb095AlphaDummy065 f)),
        ((nb095AlphaDummy064 D R S_cls E), (nb095AlphaDummy066 f)),
        ((nb095AlphaDummy056 D R S_cls E), (nb095AlphaDummy058 f)),
        ((nb095AlphaDummy055 D R S_cls E), (nb095AlphaDummy057 f)),
        ((nb095AlphaDummy061 D R S_cls E), (nb095AlphaDummy062 f)),
        ((nb095AlphaDummy059 D R S_cls E), (nb095AlphaDummy060 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy081
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy081
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0064
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy082 f) from (by
          unfold
            nb095AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy070 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0062
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy063
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071
        D R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy071
        D R S_cls E) ≠ (nb095AlphaDummy083 D R S_cls E) from (by
          unfold
            nb095AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0068
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy084 f) from (by
          unfold
            nb095AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy071 D R S_cls E) ≠
        (nb095AlphaDummy079 D R S_cls E) from (by
          unfold
            nb095AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0066
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy074 f) ≠ (nb095AlphaDummy080 f) from (by
          unfold
            nb095AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy063 D R S_cls E) ≠
        (nb095AlphaDummy067 D R S_cls E) from (by
                                          unfold nb095AlphaDummy067;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0050 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy065 f) ≠
        (nb095AlphaDummy068 f) from (by
                                          unfold nb095AlphaDummy068;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy067 D R S_cls E),
                                        (nb095AlphaDummy068 f)),
                                      ((nb095AlphaDummy063 D R S_cls E),
                                        (nb095AlphaDummy065 f)),
                                      ((nb095AlphaDummy064 D R S_cls E),
                                        (nb095AlphaDummy066 f)),
                                      ((nb095AlphaDummy056 D R S_cls E),
                                        (nb095AlphaDummy058 f)),
                                      ((nb095AlphaDummy055 D R S_cls E),
                                        (nb095AlphaDummy057 f)),
                                      ((nb095AlphaDummy061 D R S_cls E),
                                        (nb095AlphaDummy062 f)),
                                      ((nb095AlphaDummy059 D R S_cls E),
                                        (nb095AlphaDummy060 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy009 D R S_cls E),
                                        (nb095AlphaDummy010 f)),
                                      ((nb095AlphaDummy007 D R S_cls E),
                                        (nb095AlphaDummy008 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy063 D R S_cls E) ≠
                                        (nb095AlphaDummy067 D R S_cls E) from (by
                                        unfold nb095AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0050 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy068 f) from
                                      (by
                                        unfold nb095AlphaDummy068;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy063 D R S_cls E) ≠
        (nb095AlphaDummy067 D R S_cls E) from (by
                                          unfold nb095AlphaDummy067;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0050 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy065 f) ≠
        (nb095AlphaDummy068 f) from (by
                                          unfold nb095AlphaDummy068;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy067 D R S_cls E),
                                        (nb095AlphaDummy068 f)),
                                      ((nb095AlphaDummy063 D R S_cls E),
                                        (nb095AlphaDummy065 f)),
                                      ((nb095AlphaDummy064 D R S_cls E),
                                        (nb095AlphaDummy066 f)),
                                      ((nb095AlphaDummy056 D R S_cls E),
                                        (nb095AlphaDummy058 f)),
                                      ((nb095AlphaDummy055 D R S_cls E),
                                        (nb095AlphaDummy057 f)),
                                      ((nb095AlphaDummy061 D R S_cls E),
                                        (nb095AlphaDummy062 f)),
                                      ((nb095AlphaDummy059 D R S_cls E),
                                        (nb095AlphaDummy060 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy009 D R S_cls E),
                                        (nb095AlphaDummy010 f)),
                                      ((nb095AlphaDummy007 D R S_cls E),
                                        (nb095AlphaDummy008 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
