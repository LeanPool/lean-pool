/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C084C001Part003

/-! NF weak partition development: NAR4C084C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb084_split_alpha_0001`. -/
@[expose]
noncomputable def nb084SplitAlpha0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) :
    TAlphaWff
      [((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      (Wff.imp (Wff.classMem (Class.cv (nb084AlphaDummy010 A B R))
          (Class.cv (nb084AlphaDummy004 A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
            (synCun (synCphi (Class.cv (nb084AlphaDummy010 A B R))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb084AlphaDummy012 x y A R))
          (Class.cv (nb084AlphaDummy006 x y A R))) (Wff.neg
          (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
            (synCun (synCphi (Class.cv (nb084AlphaDummy012 x y A R)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
              unfold nb084AlphaDummy010;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 1))))
          (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy012 x y A R) from (by
              unfold nb084AlphaDummy012;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 1))))
          (TAlphaVar.there
            (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy009 A B R) from (by
                unfold nb084AlphaDummy009;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 0))))
            (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy011 x y A R) from (by
                unfold nb084AlphaDummy011;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 0))))
            (TAlphaVar.there
              (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy039 A B R) from (by
                  unfold nb084AlphaDummy039;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0040 A B R) 0))))
              (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy040 x y A R) from (by
                  unfold nb084AlphaDummy040;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb084_support_mem_0041 x y A R) 0)))) (TAlphaVar.there
                (show (nb084AlphaDummy004 A B R) ≠ (nb084AlphaDummy013 A B R) from (by
                    unfold nb084AlphaDummy013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb084_support_mem_0037 A B R) 0))))
                (show (nb084AlphaDummy006 x y A R) ≠ (nb084AlphaDummy014 x y A R) from (by
                    unfold nb084AlphaDummy014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb084_support_mem_0039 x y A R) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
                ((Class.cv (nb084AlphaDummy004 A B R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
                ((Class.cv (nb084AlphaDummy006 x y A R))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084AlphaDummy010 A B R) ≠
                                        (nb084AlphaDummy017 A B R) from (by
                                        unfold nb084AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0014 A B R) 0)))) (show
                                      (nb084AlphaDummy012 x y A R) ≠
                                        (nb084AlphaDummy019 x y A R) from (by
                                        unfold nb084AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0015 x y A R) 0))))
                                    (TAlphaVar.there (show (nb084AlphaDummy010 A B R) ≠
        (nb084AlphaDummy018 A B R) from (by
                                          unfold nb084AlphaDummy018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0014 A B R) 1)))) (show
                                        (nb084AlphaDummy012 x y A R) ≠
        (nb084AlphaDummy020 x y A R) from (by
                                          unfold nb084AlphaDummy020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0015 x y A R) 1))))
                                      (TAlphaVar.there (show (nb084AlphaDummy010 A B R) ≠
        (nb084AlphaDummy043 A B R) from (by
          unfold nb084AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0044 A B R) 0)))) (show (nb084AlphaDummy012 x y A R) ≠
        (nb084AlphaDummy044 x y A R) from (by
          unfold nb084AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0045 x y A R) 0)))) (TAlphaVar.there (show
        (nb084AlphaDummy010 A B R) ≠ (nb084AlphaDummy041 A B R) from (by
          unfold nb084AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0042 A B R) 0)))) (show (nb084AlphaDummy012 x y A R) ≠
        (nb084AlphaDummy042 x y A R) from (by
          unfold nb084AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0043 x y A R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb084AlphaDummy010 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb084AlphaDummy012 x y A R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy024 A B R)
        from (by
          unfold nb084AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  1)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy027 x y A R)
        from (by
          unfold nb084AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  1)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy023 A B R) from (by
          unfold nb084AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy026 x y A R)
        from (by
          unfold nb084AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold
            nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016
                    A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold
            nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy031 A B R)
        from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019
        x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy035 A B R)
        from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024
        A B R) ≠ (nb084AlphaDummy035 A B R) from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠ (nb084AlphaDummy037 A B R)
        from (by
          unfold
            nb084AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy037 A B R) from (by
          unfold
            nb084AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy021 A B R)
        from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084AlphaDummy010 A B R) ≠
                                        (nb084AlphaDummy017 A B R) from (by
                                        unfold nb084AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0014 A B R) 0)))) (show
                                      (nb084AlphaDummy012 x y A R) ≠
                                        (nb084AlphaDummy019 x y A R) from (by
                                        unfold nb084AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0015 x y A R) 0))))
                                    (TAlphaVar.there (show (nb084AlphaDummy010 A B R) ≠
        (nb084AlphaDummy018 A B R) from (by
                                          unfold nb084AlphaDummy018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0014 A B R) 1)))) (show
                                        (nb084AlphaDummy012 x y A R) ≠
        (nb084AlphaDummy020 x y A R) from (by
                                          unfold nb084AlphaDummy020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0015 x y A R) 1))))
                                      (TAlphaVar.there (show (nb084AlphaDummy010 A B R) ≠
        (nb084AlphaDummy043 A B R) from (by
          unfold nb084AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0044 A B R) 0)))) (show (nb084AlphaDummy012 x y A R) ≠
        (nb084AlphaDummy044 x y A R) from (by
          unfold nb084AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0045 x y A R) 0)))) (TAlphaVar.there (show
        (nb084AlphaDummy010 A B R) ≠ (nb084AlphaDummy041 A B R) from (by
          unfold nb084AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0042 A B R) 0)))) (show (nb084AlphaDummy012 x y A R) ≠
        (nb084AlphaDummy042 x y A R) from (by
          unfold nb084AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0043 x y A R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb084AlphaDummy010 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb084AlphaDummy012 x y A R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy024 A B R)
        from (by
          unfold nb084AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  1)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy027 x y A R)
        from (by
          unfold nb084AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  1)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy023 A B R) from (by
          unfold nb084AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy026 x y A R)
        from (by
          unfold nb084AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold
            nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016
                    A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold
            nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy031 A B R)
        from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019
        x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy035 A B R)
        from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024
        A B R) ≠ (nb084AlphaDummy035 A B R) from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠ (nb084AlphaDummy037 A B R)
        from (by
          unfold
            nb084AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy037 A B R) from (by
          unfold
            nb084AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy021 A B R)
        from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy043 A B R), (nb084AlphaDummy044 x y A R)),
        ((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb084AlphaDummy041 A B R), (nb084AlphaDummy042 x y A R)),
                    ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
                    ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
                    ((nb084AlphaDummy039 A B R), (nb084AlphaDummy040 x y A R)),
                    ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
                    ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
                    ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
                    ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
                    ((nb084AlphaDummy000 A B R), d)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb084_focused_notmem_0010 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy004 A B R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
          ((Class.cv (nb084AlphaDummy002 A B R))).fv)
        1 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0011 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy006 x y A R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0012 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy003 A B R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
          ((Class.cv (nb084AlphaDummy002 A B R))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0013 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084AlphaDummy005 x y A R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0014 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy002 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb084_focused_notmem_0015 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy001 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb084_focused_notmem_0016 (A : Class) (B : Class) (R : Class) :
    (nb084AlphaDummy000 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb084_compact_envfresh_0012 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TEnvFresh
      [((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084AlphaDummy004 A B R) (nb084AlphaDummy006 x y A R)
      (nb084_focused_notmem_0010 A B R) (nb084_focused_notmem_0011 x y A R)
      (TEnvFresh.consFresh (nb084AlphaDummy003 A B R) (nb084AlphaDummy005 x y A R)
        (nb084_focused_notmem_0012 A B R) (nb084_focused_notmem_0013 x y A R)
        (TEnvFresh.consFresh (nb084AlphaDummy002 A B R) y
          (nb084_focused_notmem_0014 A B R) dv_R_y
          (TEnvFresh.consFresh (nb084AlphaDummy001 A B R) x
            (nb084_focused_notmem_0015 A B R) dv_R_x
            (TEnvFresh.consFresh (nb084AlphaDummy000 A B R) d
              (nb084_focused_notmem_0016 A B R) dv_R_d (TEnvFresh.nil R.fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
