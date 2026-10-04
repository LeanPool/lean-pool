/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C095M3Part008Block001


/-! NF weak partition development: NAR4H5C095M3Part008. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0000`. -/
@[expose]
noncomputable def nb095SplitAlpha0000 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy025 D R S_cls E), (nb095AlphaDummy026 f)),
        ((nb095AlphaDummy023 D R S_cls E), (nb095AlphaDummy024 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
        ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy025 D R S_cls E))
          (Class.cab (nb095AlphaDummy019 D R S_cls E)
            (synWrex (nb095AlphaDummy020 D R S_cls E)
              (Class.cv (nb095AlphaDummy011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy025 D R S_cls E))
            (Class.cab (nb095AlphaDummy019 D R S_cls E)
              (synWrex (nb095AlphaDummy020 D R S_cls E)
                (Class.cv (nb095AlphaDummy011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy019 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy020 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy026 f))
          (Class.cab (nb095AlphaDummy021 f)
            (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                (synCphi (Class.cv (nb095AlphaDummy022 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy026 f))
            (Class.cab (nb095AlphaDummy021 f)
              (synWrex (nb095AlphaDummy022 f) (Class.cv (nb095AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy021 f))
                  (synCphi (Class.cv (nb095AlphaDummy022 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                      (nb095AlphaDummy020 D R S_cls E) from (by
                      unfold nb095AlphaDummy020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
                  (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy022 f) from (by
                      unfold nb095AlphaDummy022;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0006 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                        (nb095AlphaDummy019 D R S_cls E) from (by
                        unfold nb095AlphaDummy019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 0))))
                    (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy021 f) from (by
                        unfold nb095AlphaDummy021;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0006 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy011 D R S_cls E) ≠
                          (nb095AlphaDummy025 D R S_cls E) from (by
                          unfold nb095AlphaDummy025;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0008 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy026 f) from (by
                          unfold nb095AlphaDummy026;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0009 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                            (nb095AlphaDummy023 D R S_cls E) from (by
                            unfold nb095AlphaDummy023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0005 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy024 f) from (by
                            unfold nb095AlphaDummy024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0007 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv
                                  (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
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
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy025 D R S_cls E), (nb095AlphaDummy026 f)),
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
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy025 D R S_cls E), (nb095AlphaDummy026 f)),
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
                                    ((nb095AlphaDummy020 D R S_cls E),
                                      (nb095AlphaDummy022 f)),
                                    ((nb095AlphaDummy019 D R S_cls E),
                                      (nb095AlphaDummy021 f)),
                                    ((nb095AlphaDummy025 D R S_cls E),
                                      (nb095AlphaDummy026 f)),
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
                                    ((nb095AlphaDummy020 D R S_cls E),
                                      (nb095AlphaDummy022 f)),
                                    ((nb095AlphaDummy019 D R S_cls E),
                                      (nb095AlphaDummy021 f)),
                                    ((nb095AlphaDummy025 D R S_cls E),
                                      (nb095AlphaDummy026 f)),
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
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                        (nb095AlphaDummy020 D R S_cls E) from (by
                        unfold nb095AlphaDummy020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
                    (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy022 f) from (by
                        unfold nb095AlphaDummy022;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0006 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy011 D R S_cls E) ≠
                          (nb095AlphaDummy019 D R S_cls E) from (by
                          unfold nb095AlphaDummy019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy021 f) from (by
                          unfold nb095AlphaDummy021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0006 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                            (nb095AlphaDummy025 D R S_cls E) from (by
                            unfold nb095AlphaDummy025;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0008 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy026 f) from (by
                            unfold nb095AlphaDummy026;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0009 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy011 D R S_cls E) ≠
                              (nb095AlphaDummy023 D R S_cls E) from (by
                              unfold nb095AlphaDummy023;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0005 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy024 f) from (by
                              unfold nb095AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0007 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv
                                    (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy020 D R S_cls E) ≠
                                (nb095AlphaDummy027 D R S_cls E) from (by
                                unfold nb095AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0010 D R S_cls E) 0))))
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
                              (show (nb095AlphaDummy022 f) ≠ (nb095AlphaDummy030 f) from
                                (by
                                  unfold nb095AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0011 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy022 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy027 D R S_cls E) ≠ (nb095AlphaDummy034 D R S_cls E) from (by
          unfold nb095AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R
                    S_cls E)
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
                  (nb095_support_mem_0015 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy027 D R S_cls E) ≠
        (nb095AlphaDummy031 D R S_cls E) from (by
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
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy025 D R S_cls E), (nb095AlphaDummy026 f)),
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy035 D R S_cls E) ≠ (nb095AlphaDummy041
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        ((nb095AlphaDummy020 D R S_cls E), (nb095AlphaDummy022 f)),
        ((nb095AlphaDummy019 D R S_cls E), (nb095AlphaDummy021 f)),
        ((nb095AlphaDummy025 D R S_cls E), (nb095AlphaDummy026 f)),
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy045
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy035
        D R S_cls E) ≠ (nb095AlphaDummy047 D R S_cls E) from (by
          unfold
            nb095AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
                                                  (nb095_support_mem_0012 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy029 f) ≠
        (nb095AlphaDummy032 f) from (by
                                          unfold nb095AlphaDummy032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy031 D R S_cls E),
                                        (nb095AlphaDummy032 f)),
                                      ((nb095AlphaDummy027 D R S_cls E),
                                        (nb095AlphaDummy029 f)),
                                      ((nb095AlphaDummy028 D R S_cls E),
                                        (nb095AlphaDummy030 f)),
                                      ((nb095AlphaDummy020 D R S_cls E),
                                        (nb095AlphaDummy022 f)),
                                      ((nb095AlphaDummy019 D R S_cls E),
                                        (nb095AlphaDummy021 f)),
                                      ((nb095AlphaDummy025 D R S_cls E),
                                        (nb095AlphaDummy026 f)),
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
                                                  (nb095_support_mem_0012 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy029 f) ≠
        (nb095AlphaDummy032 f) from (by
                                          unfold nb095AlphaDummy032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy031 D R S_cls E),
                                        (nb095AlphaDummy032 f)),
                                      ((nb095AlphaDummy027 D R S_cls E),
                                        (nb095AlphaDummy029 f)),
                                      ((nb095AlphaDummy028 D R S_cls E),
                                        (nb095AlphaDummy030 f)),
                                      ((nb095AlphaDummy020 D R S_cls E),
                                        (nb095AlphaDummy022 f)),
                                      ((nb095AlphaDummy019 D R S_cls E),
                                        (nb095AlphaDummy021 f)),
                                      ((nb095AlphaDummy025 D R S_cls E),
                                        (nb095AlphaDummy026 f)),
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
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
