/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C084C001Block001

/-! NF weak partition development: NAR4C084C001Part003. -/


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

/-- Checked nominal proof certificate identified upstream as `nb084_split_alpha_0000`. -/
@[expose]
noncomputable def nb084SplitAlpha0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) :
    TAlphaWff
      [((nb084AlphaDummy015 A B R), (nb084AlphaDummy016 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)]
      (Wff.imp (Wff.classMem (Class.cv (nb084AlphaDummy015 A B R))
          (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
              (Class.cv (nb084AlphaDummy003 A B R))
              (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                (synCphi (Class.cv (nb084AlphaDummy010 A B R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb084AlphaDummy015 A B R))
            (Class.cab (nb084AlphaDummy009 A B R) (synWrex (nb084AlphaDummy010 A B R)
                (Class.cv (nb084AlphaDummy003 A B R))
                (Wff.classEq (Class.cv (nb084AlphaDummy009 A B R))
                  (synCphi (Class.cv (nb084AlphaDummy010 A B R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb084AlphaDummy016 x y A R))
          (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
              (Class.cv (nb084AlphaDummy005 x y A R))
              (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb084AlphaDummy016 x y A R))
            (Class.cab (nb084AlphaDummy011 x y A R) (synWrex (nb084AlphaDummy012 x y A R)
                (Class.cv (nb084AlphaDummy005 x y A R))
                (Wff.classEq (Class.cv (nb084AlphaDummy011 x y A R))
                  (synCphi (Class.cv (nb084AlphaDummy012 x y A R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
                      unfold nb084AlphaDummy010;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb084_support_mem_0008 A B R) 1))))
                  (show (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy012 x y A R) from
                    (by
                      unfold nb084AlphaDummy012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 1))))
                  (TAlphaVar.there
                    (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy009 A B R) from (by
                        unfold nb084AlphaDummy009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb084_support_mem_0008 A B R) 0)))) (show
                      (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy011 x y A R) from (by
                        unfold nb084AlphaDummy011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 0))))
                    (TAlphaVar.there
                      (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy015 A B R) from
                        (by
                          unfold nb084AlphaDummy015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb084_support_mem_0012 A B R) 0)))) (show
                        (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy016 x y A R) from
                        (by
                          unfold nb084AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb084_support_mem_0013 x y A R) 0))))
                      (TAlphaVar.there (show
                          (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy013 A B R) from (by
                            unfold nb084AlphaDummy013;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb084_support_mem_0009 A B R) 0)))) (show
                          (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy014 x y A R) from
                          (by
                            unfold nb084AlphaDummy014;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb084_support_mem_0011 x y A R) 0))))
                        (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪
                                ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
                              ((Class.cv (nb084AlphaDummy002 A B R))).fv) (by decide))
                          (freshVar_injective
                            ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
                      ((Class.cv (nb084AlphaDummy004 A B R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
                      ((Class.cv (nb084AlphaDummy006 x y A R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb084AlphaDummy010 A B R) ≠ (nb084AlphaDummy017 A B R) from
                            (by
                              unfold nb084AlphaDummy017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb084_support_mem_0014 A B R) 0)))) (show
                            (nb084AlphaDummy012 x y A R) ≠ (nb084AlphaDummy019 x y A R)
                            from (by
                              unfold nb084AlphaDummy019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb084_support_mem_0015 x y A R)
                                      0)))) (TAlphaVar.there (show
                              (nb084AlphaDummy010 A B R) ≠ (nb084AlphaDummy018 A B R) from
                              (by
                                unfold nb084AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb084_support_mem_0014 A B R)
                                        1)))) (show (nb084AlphaDummy012 x y A R) ≠
                                (nb084AlphaDummy020 x y A R) from (by
                                unfold nb084AlphaDummy020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb084_support_mem_0015 x y A R)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb084AlphaDummy010 A B R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb084AlphaDummy012 x y A R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy024 A B R)
        from (by
          unfold nb084AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018 A B R)
                  1)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy027 x y A R)
        from (by
          unfold nb084AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019 x y A R)
                  1)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy023 A B R) from (by
          unfold nb084AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy026 x y A R)
        from (by
          unfold nb084AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019 x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
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
                  (nb084_support_mem_0017 x y A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy015 A B R), (nb084AlphaDummy016 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024
        A B R) ≠ (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x y A R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠ (nb084AlphaDummy031 A B R)
        from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x y A R)
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
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x y A R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠ (nb084AlphaDummy031 A B R)
        from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy015 A B R), (nb084AlphaDummy016 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024
        A B R) ≠ (nb084AlphaDummy035 A B R) from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x y A R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy035 A B R)
        from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x y A R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy037 A B R) from (by
          unfold
            nb084AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x y A R)
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
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084AlphaDummy017 A B R) ≠
                                        (nb084AlphaDummy021 A B R) from (by
                                        unfold nb084AlphaDummy021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0016 A B R) 0)))) (show
                                      (nb084AlphaDummy019 x y A R) ≠
                                        (nb084AlphaDummy022 x y A R) from (by
                                        unfold nb084AlphaDummy022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0017 x y A R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb084AlphaDummy021 A B R),
                                      (nb084AlphaDummy022 x y A R)),
                                    ((nb084AlphaDummy017 A B R),
                                      (nb084AlphaDummy019 x y A R)),
                                    ((nb084AlphaDummy018 A B R),
                                      (nb084AlphaDummy020 x y A R)),
                                    ((nb084AlphaDummy010 A B R),
                                      (nb084AlphaDummy012 x y A R)),
                                    ((nb084AlphaDummy009 A B R),
                                      (nb084AlphaDummy011 x y A R)),
                                    ((nb084AlphaDummy015 A B R),
                                      (nb084AlphaDummy016 x y A R)),
                                    ((nb084AlphaDummy013 A B R),
                                      (nb084AlphaDummy014 x y A R)),
                                    ((nb084AlphaDummy004 A B R),
                                      (nb084AlphaDummy006 x y A R)),
                                    ((nb084AlphaDummy003 A B R),
                                      (nb084AlphaDummy005 x y A R)),
                                    ((nb084AlphaDummy002 A B R), y),
                                    ((nb084AlphaDummy001 A B R), x),
                                    ((nb084AlphaDummy000 A B R), d)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb084AlphaDummy017 A B R) ≠
                                      (nb084AlphaDummy021 A B R) from (by
                                      unfold nb084AlphaDummy021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb084_support_mem_0016 A B R) 0)))) (show
                                    (nb084AlphaDummy019 x y A R) ≠
                                      (nb084AlphaDummy022 x y A R) from (by
                                      unfold nb084AlphaDummy022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb084_support_mem_0017 x y A R) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084AlphaDummy017 A B R) ≠
                                        (nb084AlphaDummy021 A B R) from (by
                                        unfold nb084AlphaDummy021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0016 A B R) 0)))) (show
                                      (nb084AlphaDummy019 x y A R) ≠
                                        (nb084AlphaDummy022 x y A R) from (by
                                        unfold nb084AlphaDummy022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0017 x y A R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb084AlphaDummy021 A B R),
                                      (nb084AlphaDummy022 x y A R)),
                                    ((nb084AlphaDummy017 A B R),
                                      (nb084AlphaDummy019 x y A R)),
                                    ((nb084AlphaDummy018 A B R),
                                      (nb084AlphaDummy020 x y A R)),
                                    ((nb084AlphaDummy010 A B R),
                                      (nb084AlphaDummy012 x y A R)),
                                    ((nb084AlphaDummy009 A B R),
                                      (nb084AlphaDummy011 x y A R)),
                                    ((nb084AlphaDummy015 A B R),
                                      (nb084AlphaDummy016 x y A R)),
                                    ((nb084AlphaDummy013 A B R),
                                      (nb084AlphaDummy014 x y A R)),
                                    ((nb084AlphaDummy004 A B R),
                                      (nb084AlphaDummy006 x y A R)),
                                    ((nb084AlphaDummy003 A B R),
                                      (nb084AlphaDummy005 x y A R)),
                                    ((nb084AlphaDummy002 A B R), y),
                                    ((nb084AlphaDummy001 A B R), x),
                                    ((nb084AlphaDummy000 A B R), d)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy010 A B R) from (by
                        unfold nb084AlphaDummy010;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb084_support_mem_0008 A B R) 1)))) (show
                      (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy012 x y A R) from (by
                        unfold nb084AlphaDummy012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 1))))
                    (TAlphaVar.there
                      (show (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy009 A B R) from
                        (by
                          unfold nb084AlphaDummy009;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb084_support_mem_0008 A B R) 0)))) (show
                        (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy011 x y A R) from
                        (by
                          unfold nb084AlphaDummy011;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb084_support_mem_0010 x y A R) 0))))
                      (TAlphaVar.there (show
                          (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy015 A B R) from (by
                            unfold nb084AlphaDummy015;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb084_support_mem_0012 A B R) 0)))) (show
                          (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy016 x y A R) from
                          (by
                            unfold nb084AlphaDummy016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb084_support_mem_0013 x y A R) 0))))
                        (TAlphaVar.there (show
                            (nb084AlphaDummy003 A B R) ≠ (nb084AlphaDummy013 A B R) from
                            (by
                              unfold nb084AlphaDummy013;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb084_support_mem_0009 A B R) 0)))) (show
                            (nb084AlphaDummy005 x y A R) ≠ (nb084AlphaDummy014 x y A R)
                            from (by
                              unfold nb084AlphaDummy014;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb084_support_mem_0011 x y A R)
                                      0)))) (TAlphaVar.there (freshVar_injective
                              ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084AlphaDummy001 A B R))).fv ∪
                                ((Class.cv (nb084AlphaDummy002 A B R))).fv) (by decide))
                            (freshVar_injective
                              ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb084AlphaDummy003 A B R))).fv ∪
                        ((Class.cv (nb084AlphaDummy004 A B R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb084AlphaDummy005 x y A R))).fv ∪
                        ((Class.cv (nb084AlphaDummy006 x y A R))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy010 A B R) ≠
                                (nb084AlphaDummy017 A B R) from (by
                                unfold nb084AlphaDummy017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb084_support_mem_0014 A B R)
                                        0)))) (show (nb084AlphaDummy012 x y A R) ≠
                                (nb084AlphaDummy019 x y A R) from (by
                                unfold nb084AlphaDummy019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb084_support_mem_0015 x y A R)
                                        0)))) (TAlphaVar.there (show
                                (nb084AlphaDummy010 A B R) ≠ (nb084AlphaDummy018 A B R)
                                from (by
                                  unfold nb084AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb084_support_mem_0014 A B R)
                                          1)))) (show (nb084AlphaDummy012 x y A R) ≠
                                  (nb084AlphaDummy020 x y A R) from (by
                                  unfold nb084AlphaDummy020;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb084_support_mem_0015 x y A R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb084AlphaDummy010 A B R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb084AlphaDummy012 x y A R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb084AlphaDummy017 A B R) ≠ (nb084AlphaDummy024 A B R) from (by
          unfold nb084AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018 A B R)
                  1)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy027 x y A R)
        from (by
          unfold nb084AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019 x y A R)
                  1)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy023 A B R) from (by
          unfold nb084AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018 A B R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy026 x y A R)
        from (by
          unfold nb084AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019 x y A
                    R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
          unfold nb084AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B
                    R)
                  0)))) (show (nb084AlphaDummy019 x y A R) ≠ (nb084AlphaDummy022 x y A R)
        from (by
          unfold nb084AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y
                    A R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy015 A B R), (nb084AlphaDummy016 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024
        A B R) ≠ (nb084AlphaDummy031 A B R) from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x y A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠ (nb084AlphaDummy031 A B R)
        from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x y A
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
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x y A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠ (nb084AlphaDummy031 A B R)
        from (by
          unfold
            nb084AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy032 x y A R)
        from (by
          unfold
            nb084AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy029 A B R) from (by
          unfold
            nb084AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy030 x y A R)
        from (by
          unfold
            nb084AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x y A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb084AlphaDummy025 A B R), (nb084AlphaDummy028 x y A R)),
        ((nb084AlphaDummy024 A B R), (nb084AlphaDummy027 x y A R)),
        ((nb084AlphaDummy023 A B R), (nb084AlphaDummy026 x y A R)),
        ((nb084AlphaDummy021 A B R), (nb084AlphaDummy022 x y A R)),
        ((nb084AlphaDummy017 A B R), (nb084AlphaDummy019 x y A R)),
        ((nb084AlphaDummy018 A B R), (nb084AlphaDummy020 x y A R)),
        ((nb084AlphaDummy010 A B R), (nb084AlphaDummy012 x y A R)),
        ((nb084AlphaDummy009 A B R), (nb084AlphaDummy011 x y A R)),
        ((nb084AlphaDummy015 A B R), (nb084AlphaDummy016 x y A R)),
        ((nb084AlphaDummy013 A B R), (nb084AlphaDummy014 x y A R)),
        ((nb084AlphaDummy004 A B R), (nb084AlphaDummy006 x y A R)),
        ((nb084AlphaDummy003 A B R), (nb084AlphaDummy005 x y A R)),
        ((nb084AlphaDummy002 A B R), y), ((nb084AlphaDummy001 A B R), x),
        ((nb084AlphaDummy000 A B R), d)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb084AlphaDummy017 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy024
        A B R) ≠ (nb084AlphaDummy035 A B R) from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x y A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠ (nb084AlphaDummy035 A B R)
        from (by
          unfold
            nb084AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy036 x y A R)
        from (by
          unfold
            nb084AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy024 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A B R)
                  0)))) (show (nb084AlphaDummy027 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x y A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084AlphaDummy017
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb084AlphaDummy019 x y A R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084AlphaDummy025
        A B R) ≠ (nb084AlphaDummy037 A B R) from (by
          unfold
            nb084AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x y A
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
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy038 x y A R)
        from (by
          unfold
            nb084AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084AlphaDummy025 A B R) ≠
        (nb084AlphaDummy033 A B R) from (by
          unfold
            nb084AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A B R)
                  0)))) (show (nb084AlphaDummy028 x y A R) ≠ (nb084AlphaDummy034 x y A R)
        from (by
          unfold
            nb084AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x y A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
                                          unfold nb084AlphaDummy021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0016 A B R) 0)))) (show
                                        (nb084AlphaDummy019 x y A R) ≠
        (nb084AlphaDummy022 x y A R) from (by
                                          unfold nb084AlphaDummy022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0017 x y A R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb084AlphaDummy021 A B R),
                                        (nb084AlphaDummy022 x y A R)),
                                      ((nb084AlphaDummy017 A B R),
                                        (nb084AlphaDummy019 x y A R)),
                                      ((nb084AlphaDummy018 A B R),
                                        (nb084AlphaDummy020 x y A R)),
                                      ((nb084AlphaDummy010 A B R),
                                        (nb084AlphaDummy012 x y A R)),
                                      ((nb084AlphaDummy009 A B R),
                                        (nb084AlphaDummy011 x y A R)),
                                      ((nb084AlphaDummy015 A B R),
                                        (nb084AlphaDummy016 x y A R)),
                                      ((nb084AlphaDummy013 A B R),
                                        (nb084AlphaDummy014 x y A R)),
                                      ((nb084AlphaDummy004 A B R),
                                        (nb084AlphaDummy006 x y A R)),
                                      ((nb084AlphaDummy003 A B R),
                                        (nb084AlphaDummy005 x y A R)),
                                      ((nb084AlphaDummy002 A B R), y),
                                      ((nb084AlphaDummy001 A B R), x),
                                      ((nb084AlphaDummy000 A B R), d)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084AlphaDummy017 A B R) ≠
                                        (nb084AlphaDummy021 A B R) from (by
                                        unfold nb084AlphaDummy021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0016 A B R) 0)))) (show
                                      (nb084AlphaDummy019 x y A R) ≠
                                        (nb084AlphaDummy022 x y A R) from (by
                                        unfold nb084AlphaDummy022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0017 x y A R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb084AlphaDummy017 A B R) ≠
        (nb084AlphaDummy021 A B R) from (by
                                          unfold nb084AlphaDummy021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0016 A B R) 0)))) (show
                                        (nb084AlphaDummy019 x y A R) ≠
        (nb084AlphaDummy022 x y A R) from (by
                                          unfold nb084AlphaDummy022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0017 x y A R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb084AlphaDummy021 A B R),
                                        (nb084AlphaDummy022 x y A R)),
                                      ((nb084AlphaDummy017 A B R),
                                        (nb084AlphaDummy019 x y A R)),
                                      ((nb084AlphaDummy018 A B R),
                                        (nb084AlphaDummy020 x y A R)),
                                      ((nb084AlphaDummy010 A B R),
                                        (nb084AlphaDummy012 x y A R)),
                                      ((nb084AlphaDummy009 A B R),
                                        (nb084AlphaDummy011 x y A R)),
                                      ((nb084AlphaDummy015 A B R),
                                        (nb084AlphaDummy016 x y A R)),
                                      ((nb084AlphaDummy013 A B R),
                                        (nb084AlphaDummy014 x y A R)),
                                      ((nb084AlphaDummy004 A B R),
                                        (nb084AlphaDummy006 x y A R)),
                                      ((nb084AlphaDummy003 A B R),
                                        (nb084AlphaDummy005 x y A R)),
                                      ((nb084AlphaDummy002 A B R), y),
                                      ((nb084AlphaDummy001 A B R), x),
                                      ((nb084AlphaDummy000 A B R), d)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
