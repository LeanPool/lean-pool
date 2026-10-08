/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C077C001Part009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0000`. -/
@[expose]
noncomputable def nb077SplitAlpha0000 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy025 F I), (nb077AlphaDummy026 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy025 F I))
          (Class.cab (nb077AlphaDummy019 F I)
            (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                (synCphi (Class.cv (nb077AlphaDummy020 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy025 F I))
            (Class.cab (nb077AlphaDummy019 F I)
              (synWrex (nb077AlphaDummy020 F I) (Class.cv (nb077AlphaDummy016 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy019 F I))
                  (synCphi (Class.cv (nb077AlphaDummy020 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy026 x F I))
          (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
              (Class.cv (nb077AlphaDummy018 x F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy026 x F I))
            (Class.cab (nb077AlphaDummy021 x F I) (synWrex (nb077AlphaDummy022 x F I)
                (Class.cv (nb077AlphaDummy018 x F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy021 x F I))
                  (synCphi (Class.cv (nb077AlphaDummy022 x F I))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy020 F I) from (by
                      unfold nb077AlphaDummy020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
                  (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy022 x F I) from (by
                      unfold nb077AlphaDummy022;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy019 F I) from (by
                        unfold nb077AlphaDummy019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
                    (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy021 x F I) from (by
                        unfold nb077AlphaDummy021;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
                    (TAlphaVar.there
                      (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy025 F I) from (by
                          unfold nb077AlphaDummy025;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0014 F I) 0))))
                      (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy026 x F I) from
                        (by
                          unfold nb077AlphaDummy026;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0015 x F I) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy023 F I) from (by
                            unfold nb077AlphaDummy023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0011 F I) 0)))) (show
                          (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy024 x F I) from (by
                            unfold nb077AlphaDummy024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0013 x F I) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy015 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy017 x F I))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy027 F I) from
                            (by
                              unfold nb077AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                            (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy029 x F I) from
                            (by
                              unfold nb077AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy028 F I) from (by
                                unfold nb077AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)))) (show
                              (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy030 x F I) from
                              (by
                                unfold nb077AlphaDummy030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy020 F I))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb077AlphaDummy022 x F I))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy034 F I) from
        (by
          unfold nb077AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I) 1)))) (show (nb077AlphaDummy029 x F I) ≠
        (nb077AlphaDummy037 x F I) from (by
          unfold nb077AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy033 F I) from (by
          unfold nb077AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy036 x F I) from
        (by
          unfold nb077AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy031 F I) from (by
          unfold nb077AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy032 x F I) from
        (by
          unfold nb077AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy025 F I), (nb077AlphaDummy026 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy025 F I), (nb077AlphaDummy026 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F
        I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy034
        F I) ≠ (nb077AlphaDummy045 F I) from (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy045 F I) from
        (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
                                    ((nb077AlphaDummy027 F I),
                                      (nb077AlphaDummy029 x F I)),
                                    ((nb077AlphaDummy028 F I),
                                      (nb077AlphaDummy030 x F I)),
                                    ((nb077AlphaDummy020 F I),
                                      (nb077AlphaDummy022 x F I)),
                                    ((nb077AlphaDummy019 F I),
                                      (nb077AlphaDummy021 x F I)),
                                    ((nb077AlphaDummy025 F I),
                                      (nb077AlphaDummy026 x F I)),
                                    ((nb077AlphaDummy023 F I),
                                      (nb077AlphaDummy024 x F I)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                    from (by
                                      unfold nb077AlphaDummy031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0018 F I)
                                              0)))) (show (nb077AlphaDummy029 x F I) ≠
                                      (nb077AlphaDummy032 x F I) from (by
                                      unfold nb077AlphaDummy032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0019 x F I) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
                                    ((nb077AlphaDummy027 F I),
                                      (nb077AlphaDummy029 x F I)),
                                    ((nb077AlphaDummy028 F I),
                                      (nb077AlphaDummy030 x F I)),
                                    ((nb077AlphaDummy020 F I),
                                      (nb077AlphaDummy022 x F I)),
                                    ((nb077AlphaDummy019 F I),
                                      (nb077AlphaDummy021 x F I)),
                                    ((nb077AlphaDummy025 F I),
                                      (nb077AlphaDummy026 x F I)),
                                    ((nb077AlphaDummy023 F I),
                                      (nb077AlphaDummy024 x F I)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy020 F I) from (by
                        unfold nb077AlphaDummy020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
                    (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy022 x F I) from (by
                        unfold nb077AlphaDummy022;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
                    (TAlphaVar.there
                      (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy019 F I) from (by
                          unfold nb077AlphaDummy019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
                      (show (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy021 x F I) from
                        (by
                          unfold nb077AlphaDummy021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy025 F I) from (by
                            unfold nb077AlphaDummy025;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0014 F I) 0)))) (show
                          (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy026 x F I) from (by
                            unfold nb077AlphaDummy026;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0015 x F I) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy016 F I) ≠ (nb077AlphaDummy023 F I) from
                            (by
                              unfold nb077AlphaDummy023;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0011 F I) 0)))) (show
                            (nb077AlphaDummy018 x F I) ≠ (nb077AlphaDummy024 x F I) from
                            (by
                              unfold nb077AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0013 x F I) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy015 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy017 x F I))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy027 F I) from (by
                                unfold nb077AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                              (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy029 x F I) from
                              (by
                                unfold nb077AlphaDummy029;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        0)))) (TAlphaVar.there (show
                                (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy028 F I) from
                                (by
                                  unfold nb077AlphaDummy028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                          1)))) (show (nb077AlphaDummy022 x F I) ≠
                                  (nb077AlphaDummy030 x F I) from (by
                                  unfold nb077AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy020 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy022 x F I))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy034 F I) from (by
          unfold nb077AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  1)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy037 x F I) from
        (by
          unfold nb077AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy033 F I) from (by
          unfold nb077AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy036 x F I) from
        (by
          unfold nb077AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy031 F I) from (by
          unfold nb077AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy032 x F I) from
        (by
          unfold nb077AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy025 F I), (nb077AlphaDummy026 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy025 F I), (nb077AlphaDummy026 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F
        I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy034
        F I) ≠ (nb077AlphaDummy045 F I) from (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy045 F I) from
        (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy031 F I) from (by
                                          unfold nb077AlphaDummy031;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0018 F I) 0)))) (show
                                        (nb077AlphaDummy029 x F I) ≠
        (nb077AlphaDummy032 x F I) from (by
                                          unfold nb077AlphaDummy032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0019 x F I) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy031 F I),
                                        (nb077AlphaDummy032 x F I)),
                                      ((nb077AlphaDummy027 F I),
                                        (nb077AlphaDummy029 x F I)),
                                      ((nb077AlphaDummy028 F I),
                                        (nb077AlphaDummy030 x F I)),
                                      ((nb077AlphaDummy020 F I),
                                        (nb077AlphaDummy022 x F I)),
                                      ((nb077AlphaDummy019 F I),
                                        (nb077AlphaDummy021 x F I)),
                                      ((nb077AlphaDummy025 F I),
                                        (nb077AlphaDummy026 x F I)),
                                      ((nb077AlphaDummy023 F I),
                                        (nb077AlphaDummy024 x F I)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy031 F I) from (by
                                          unfold nb077AlphaDummy031;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0018 F I) 0)))) (show
                                        (nb077AlphaDummy029 x F I) ≠
        (nb077AlphaDummy032 x F I) from (by
                                          unfold nb077AlphaDummy032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0019 x F I) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy031 F I),
                                        (nb077AlphaDummy032 x F I)),
                                      ((nb077AlphaDummy027 F I),
                                        (nb077AlphaDummy029 x F I)),
                                      ((nb077AlphaDummy028 F I),
                                        (nb077AlphaDummy030 x F I)),
                                      ((nb077AlphaDummy020 F I),
                                        (nb077AlphaDummy022 x F I)),
                                      ((nb077AlphaDummy019 F I),
                                        (nb077AlphaDummy021 x F I)),
                                      ((nb077AlphaDummy025 F I),
                                        (nb077AlphaDummy026 x F I)),
                                      ((nb077AlphaDummy023 F I),
                                        (nb077AlphaDummy024 x F I)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part011`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0001`. -/
@[expose]
noncomputable def nb077SplitAlpha0001 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy051 F I), (nb077AlphaDummy052 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy049 F I), (nb077AlphaDummy050 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy051 F I))
          (synCcompl (synCphi (Class.cv (nb077AlphaDummy020 F I))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy051 F I))
            (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy052 x F I))
          (synCcompl (synCphi (Class.cv (nb077AlphaDummy022 x F I))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy052 x F I))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy027 F I) from
                            (by
                              unfold nb077AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                            (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy029 x F I) from
                            (by
                              unfold nb077AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy028 F I) from (by
                                unfold nb077AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)))) (show
                              (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy030 x F I) from
                              (by
                                unfold nb077AlphaDummy030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        1)))) (TAlphaVar.there (show
                                (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy053 F I) from
                                (by
                                  unfold nb077AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0046 F I)
                                          0)))) (show (nb077AlphaDummy022 x F I) ≠
                                  (nb077AlphaDummy054 x F I) from (by
                                  unfold nb077AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0047 x F I)
                                          0)))) (TAlphaVar.there (show
                                  (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy051 F I) from
                                  (by
                                    unfold nb077AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0044 F I)
                                            0)))) (show (nb077AlphaDummy022 x F I) ≠
                                    (nb077AlphaDummy052 x F I) from (by
                                    unfold nb077AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0045 x F I)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy020 F I))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb077AlphaDummy022 x F I))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy034 F I) from
        (by
          unfold nb077AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I) 1)))) (show (nb077AlphaDummy029 x F I) ≠
        (nb077AlphaDummy037 x F I) from (by
          unfold nb077AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy033 F I) from (by
          unfold nb077AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy036 x F I) from
        (by
          unfold nb077AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy031 F I) from (by
          unfold nb077AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy032 x F I) from
        (by
          unfold nb077AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy053 F I), (nb077AlphaDummy054 x F I)),
        ((nb077AlphaDummy051 F I), (nb077AlphaDummy052 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy049 F I), (nb077AlphaDummy050 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy053 F I), (nb077AlphaDummy054 x F I)),
        ((nb077AlphaDummy051 F I), (nb077AlphaDummy052 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy049 F I), (nb077AlphaDummy050 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F
        I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy034
        F I) ≠ (nb077AlphaDummy045 F I) from (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy045 F I) from
        (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
                                    ((nb077AlphaDummy027 F I),
                                      (nb077AlphaDummy029 x F I)),
                                    ((nb077AlphaDummy028 F I),
                                      (nb077AlphaDummy030 x F I)),
                                    ((nb077AlphaDummy053 F I),
                                      (nb077AlphaDummy054 x F I)),
                                    ((nb077AlphaDummy051 F I),
                                      (nb077AlphaDummy052 x F I)),
                                    ((nb077AlphaDummy020 F I),
                                      (nb077AlphaDummy022 x F I)),
                                    ((nb077AlphaDummy019 F I),
                                      (nb077AlphaDummy021 x F I)),
                                    ((nb077AlphaDummy049 F I),
                                      (nb077AlphaDummy050 x F I)),
                                    ((nb077AlphaDummy023 F I),
                                      (nb077AlphaDummy024 x F I)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                    from (by
                                      unfold nb077AlphaDummy031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0018 F I)
                                              0)))) (show (nb077AlphaDummy029 x F I) ≠
                                      (nb077AlphaDummy032 x F I) from (by
                                      unfold nb077AlphaDummy032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0019 x F I) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
                                    ((nb077AlphaDummy027 F I),
                                      (nb077AlphaDummy029 x F I)),
                                    ((nb077AlphaDummy028 F I),
                                      (nb077AlphaDummy030 x F I)),
                                    ((nb077AlphaDummy053 F I),
                                      (nb077AlphaDummy054 x F I)),
                                    ((nb077AlphaDummy051 F I),
                                      (nb077AlphaDummy052 x F I)),
                                    ((nb077AlphaDummy020 F I),
                                      (nb077AlphaDummy022 x F I)),
                                    ((nb077AlphaDummy019 F I),
                                      (nb077AlphaDummy021 x F I)),
                                    ((nb077AlphaDummy049 F I),
                                      (nb077AlphaDummy050 x F I)),
                                    ((nb077AlphaDummy023 F I),
                                      (nb077AlphaDummy024 x F I)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy027 F I) from
                            (by
                              unfold nb077AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                            (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy029 x F I) from
                            (by
                              unfold nb077AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy028 F I) from (by
                                unfold nb077AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)))) (show
                              (nb077AlphaDummy022 x F I) ≠ (nb077AlphaDummy030 x F I) from
                              (by
                                unfold nb077AlphaDummy030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        1)))) (TAlphaVar.there (show
                                (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy053 F I) from
                                (by
                                  unfold nb077AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0046 F I)
                                          0)))) (show (nb077AlphaDummy022 x F I) ≠
                                  (nb077AlphaDummy054 x F I) from (by
                                  unfold nb077AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0047 x F I)
                                          0)))) (TAlphaVar.there (show
                                  (nb077AlphaDummy020 F I) ≠ (nb077AlphaDummy051 F I) from
                                  (by
                                    unfold nb077AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0044 F I)
                                            0)))) (show (nb077AlphaDummy022 x F I) ≠
                                    (nb077AlphaDummy052 x F I) from (by
                                    unfold nb077AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0045 x F I)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy020 F I))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb077AlphaDummy022 x F I))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy034 F I) from
        (by
          unfold nb077AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I) 1)))) (show (nb077AlphaDummy029 x F I) ≠
        (nb077AlphaDummy037 x F I) from (by
          unfold nb077AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy033 F I) from (by
          unfold nb077AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy036 x F I) from
        (by
          unfold nb077AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy027 F I) ≠
        (nb077AlphaDummy031 F I) from (by
          unfold nb077AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077AlphaDummy029 x F I) ≠ (nb077AlphaDummy032 x F I) from
        (by
          unfold nb077AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy053 F I), (nb077AlphaDummy054 x F I)),
        ((nb077AlphaDummy051 F I), (nb077AlphaDummy052 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy049 F I), (nb077AlphaDummy050 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠ (nb077AlphaDummy041 F I) from
        (by
          unfold
            nb077AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy042 x F I) from
        (by
          unfold
            nb077AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy039 F I) from (by
          unfold
            nb077AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy040 x F I) from
        (by
          unfold
            nb077AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy035 F I), (nb077AlphaDummy038 x F I)),
        ((nb077AlphaDummy034 F I), (nb077AlphaDummy037 x F I)),
        ((nb077AlphaDummy033 F I), (nb077AlphaDummy036 x F I)),
        ((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
        ((nb077AlphaDummy027 F I), (nb077AlphaDummy029 x F I)),
        ((nb077AlphaDummy028 F I), (nb077AlphaDummy030 x F I)),
        ((nb077AlphaDummy053 F I), (nb077AlphaDummy054 x F I)),
        ((nb077AlphaDummy051 F I), (nb077AlphaDummy052 x F I)),
        ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
        ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
        ((nb077AlphaDummy049 F I), (nb077AlphaDummy050 x F I)),
        ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy029 x F
        I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy027 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy034
        F I) ≠ (nb077AlphaDummy045 F I) from (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠ (nb077AlphaDummy045 F I) from
        (by
          unfold
            nb077AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy046 x F I) from
        (by
          unfold
            nb077AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy034 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077AlphaDummy037 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy027
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy029 x F I))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy035
        F I) ≠ (nb077AlphaDummy047 F I) from (by
          unfold
            nb077AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy048 x F I) from
        (by
          unfold
            nb077AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy035 F I) ≠
        (nb077AlphaDummy043 F I) from (by
          unfold
            nb077AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077AlphaDummy038 x F I) ≠ (nb077AlphaDummy044 x F I) from
        (by
          unfold
            nb077AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
                                    ((nb077AlphaDummy027 F I),
                                      (nb077AlphaDummy029 x F I)),
                                    ((nb077AlphaDummy028 F I),
                                      (nb077AlphaDummy030 x F I)),
                                    ((nb077AlphaDummy053 F I),
                                      (nb077AlphaDummy054 x F I)),
                                    ((nb077AlphaDummy051 F I),
                                      (nb077AlphaDummy052 x F I)),
                                    ((nb077AlphaDummy020 F I),
                                      (nb077AlphaDummy022 x F I)),
                                    ((nb077AlphaDummy019 F I),
                                      (nb077AlphaDummy021 x F I)),
                                    ((nb077AlphaDummy049 F I),
                                      (nb077AlphaDummy050 x F I)),
                                    ((nb077AlphaDummy023 F I),
                                      (nb077AlphaDummy024 x F I)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                    from (by
                                      unfold nb077AlphaDummy031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0018 F I)
                                              0)))) (show (nb077AlphaDummy029 x F I) ≠
                                      (nb077AlphaDummy032 x F I) from (by
                                      unfold nb077AlphaDummy032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0019 x F I) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy027 F I) ≠ (nb077AlphaDummy031 F I)
                                      from (by
                                        unfold nb077AlphaDummy031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077AlphaDummy029 x F I) ≠
                                        (nb077AlphaDummy032 x F I) from (by
                                        unfold nb077AlphaDummy032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb077AlphaDummy031 F I), (nb077AlphaDummy032 x F I)),
                                    ((nb077AlphaDummy027 F I),
                                      (nb077AlphaDummy029 x F I)),
                                    ((nb077AlphaDummy028 F I),
                                      (nb077AlphaDummy030 x F I)),
                                    ((nb077AlphaDummy053 F I),
                                      (nb077AlphaDummy054 x F I)),
                                    ((nb077AlphaDummy051 F I),
                                      (nb077AlphaDummy052 x F I)),
                                    ((nb077AlphaDummy020 F I),
                                      (nb077AlphaDummy022 x F I)),
                                    ((nb077AlphaDummy019 F I),
                                      (nb077AlphaDummy021 x F I)),
                                    ((nb077AlphaDummy049 F I),
                                      (nb077AlphaDummy050 x F I)),
                                    ((nb077AlphaDummy023 F I),
                                      (nb077AlphaDummy024 x F I)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed
          [((nb077AlphaDummy051 F I), (nb077AlphaDummy052 x F I)),
            ((nb077AlphaDummy020 F I), (nb077AlphaDummy022 x F I)),
            ((nb077AlphaDummy019 F I), (nb077AlphaDummy021 x F I)),
            ((nb077AlphaDummy049 F I), (nb077AlphaDummy050 x F I)),
            ((nb077AlphaDummy023 F I), (nb077AlphaDummy024 x F I)),
            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb077_compact_fv_empty_0064 (F : Class) (I : Class) :
    (nb077AlphaDummy060 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0065 (x : Var) :
    (nb077AlphaDummy063 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0066 (F : Class) (I : Class) :
    (nb077AlphaDummy059 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0067 (x : Var) :
    (nb077AlphaDummy062 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0068 (F : Class) (I : Class) :
    (nb077AlphaDummy065 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0069 (x : Var) :
    (nb077AlphaDummy066 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0070 (F : Class) (I : Class) :
    (nb077AlphaDummy057 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0071 (x : Var) (F : Class) :
    (nb077AlphaDummy058 x F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0072 (F : Class) (I : Class) :
    (nb077AlphaDummy055 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0073 (x : Var) (F : Class) :
    (nb077AlphaDummy056 x F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
