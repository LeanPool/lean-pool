/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR5H088P001Block001

/-! NF weak partition development: NAR5H088P001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb088_split_alpha_0000`. -/
@[expose]
noncomputable def nb088SplitAlpha0000 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u),
        ((nb088AlphaDummy003 A B C R), (nb088AlphaDummy004 u A B C R))]
      (Wff.neg (Wff.classMem (Class.cv (nb088AlphaDummy035 A B C R))
          (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb088AlphaDummy036 u A B C R))
          (Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy006 A B C R) from
                    (by
                      unfold nb088AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1)))) (show
                    (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy008 u A B C R) from
                    (by
                      unfold nb088AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))))
                  (TAlphaVar.there (show
                      (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy005 A B C R) from (by
                        unfold nb088AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0)))) (show
                      (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy007 u A B C R) from
                      (by
                        unfold nb088AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))))
                    (TAlphaVar.there (show
                        (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy035 A B C R) from
                        (by
                          unfold nb088AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0038 A B C R) 0)))) (show
                        (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy036 u A B C R)
                        from (by
                          unfold nb088AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0039 u A B C R) 0))))
                      (TAlphaVar.there (show (nb088AlphaDummy001 A B C R) ≠
                            (nb088AlphaDummy009 A B C R) from (by
                            unfold nb088AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0035 A B C R) 0)))) (show
                          (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy010 u A B C R)
                          from (by
                            unfold nb088AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0037 u A B C R)
                                    0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
                      ((Class.cv (nb088AlphaDummy001 A B C R))).fv) (by decide))
                  (freshVar_injective (((Class.cv u)).fv ∪
                      ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy013 A B C R) from (by
          unfold nb088AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy015 u A B C R) from (by
          unfold nb088AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy014 A B C R) from (by
          unfold nb088AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  1)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy016 u A B C R) from (by
          unfold nb088AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy039 A B C R) from (by
          unfold nb088AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy040 u A B C R) from (by
          unfold nb088AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy037 A B C R) from (by
          unfold nb088AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy038 u A B C R) from (by
          unfold nb088AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088AlphaDummy008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy013 A B C R) ≠ (nb088AlphaDummy020 A B C R) from (by
          unfold
            nb088AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  1)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy023 u A
        B C R) from (by
          unfold
            nb088AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy019 A B C R) from (by
          unfold
            nb088AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy022 u
        A B C R) from (by
          unfold
            nb088AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold
            nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy018
        u A B C R) from (by
          unfold
            nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015
                    u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R)
        from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A
        B C R) ≠ (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠ (nb088AlphaDummy033 A B C R)
        from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy033 A B C R) from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy013 A B C R) from (by
          unfold nb088AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy015 u A B C R) from (by
          unfold nb088AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy014 A B C R) from (by
          unfold nb088AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  1)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy016 u A B C R) from (by
          unfold nb088AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy039 A B C R) from (by
          unfold nb088AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy040 u A B C R) from (by
          unfold nb088AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy037 A B C R) from (by
          unfold nb088AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy038 u A B C R) from (by
          unfold nb088AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088AlphaDummy008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy013 A B C R) ≠ (nb088AlphaDummy020 A B C R) from (by
          unfold
            nb088AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  1)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy023 u A
        B C R) from (by
          unfold
            nb088AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy019 A B C R) from (by
          unfold
            nb088AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy022 u
        A B C R) from (by
          unfold
            nb088AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold
            nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy018
        u A B C R) from (by
          unfold
            nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015
                    u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R)
        from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A
        B C R) ≠ (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠ (nb088AlphaDummy033 A B C R)
        from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy033 A B C R) from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed [((nb088AlphaDummy037 A B C R),
                            (nb088AlphaDummy038 u A B C R)),
                          ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
                          ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
                          ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
                          ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
                          ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
                          ((nb088AlphaDummy000 A B C R), u),
                          ((nb088AlphaDummy003 A B C R), (nb088AlphaDummy004 u A B C R))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb088_split_alpha_0001`. -/
@[expose]
noncomputable def nb088SplitAlpha0001 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u),
        ((nb088AlphaDummy003 A B C R), (nb088AlphaDummy004 u A B C R))]
      (Wff.imp (Wff.classMem (Class.cv (nb088AlphaDummy035 A B C R))
          (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
              (Class.cv (nb088AlphaDummy001 A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb088AlphaDummy035 A B C R))
            (Class.cab (nb088AlphaDummy005 A B C R) (synWrex (nb088AlphaDummy006 A B C R)
                (Class.cv (nb088AlphaDummy001 A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy005 A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy006 A B C R)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb088AlphaDummy036 u A B C R))
          (Class.cab (nb088AlphaDummy007 u A B C R)
            (synWrex (nb088AlphaDummy008 u A B C R)
              (Class.cv (nb088AlphaDummy002 u A B C R))
              (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb088AlphaDummy036 u A B C R))
            (Class.cab (nb088AlphaDummy007 u A B C R)
              (synWrex (nb088AlphaDummy008 u A B C R)
                (Class.cv (nb088AlphaDummy002 u A B C R))
                (Wff.classEq (Class.cv (nb088AlphaDummy007 u A B C R))
                  (synCun (synCphi (Class.cv (nb088AlphaDummy008 u A B C R)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy006 A B C R) from
                    (by
                      unfold nb088AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1)))) (show
                    (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy008 u A B C R) from
                    (by
                      unfold nb088AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))))
                  (TAlphaVar.there (show
                      (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy005 A B C R) from (by
                        unfold nb088AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0)))) (show
                      (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy007 u A B C R) from
                      (by
                        unfold nb088AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))))
                    (TAlphaVar.there (show
                        (nb088AlphaDummy001 A B C R) ≠ (nb088AlphaDummy035 A B C R) from
                        (by
                          unfold nb088AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0038 A B C R) 0)))) (show
                        (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy036 u A B C R)
                        from (by
                          unfold nb088AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0039 u A B C R) 0))))
                      (TAlphaVar.there (show (nb088AlphaDummy001 A B C R) ≠
                            (nb088AlphaDummy009 A B C R) from (by
                            unfold nb088AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0035 A B C R) 0)))) (show
                          (nb088AlphaDummy002 u A B C R) ≠ (nb088AlphaDummy010 u A B C R)
                          from (by
                            unfold nb088AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0037 u A B C R)
                                    0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb088AlphaDummy000 A B C R))).fv ∪
                      ((Class.cv (nb088AlphaDummy001 A B C R))).fv) (by decide))
                  (freshVar_injective (((Class.cv u)).fv ∪
                      ((Class.cv (nb088AlphaDummy002 u A B C R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy013 A B C R) from (by
          unfold nb088AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy015 u A B C R) from (by
          unfold nb088AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy014 A B C R) from (by
          unfold nb088AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  1)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy016 u A B C R) from (by
          unfold nb088AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy039 A B C R) from (by
          unfold nb088AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy040 u A B C R) from (by
          unfold nb088AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy037 A B C R) from (by
          unfold nb088AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy038 u A B C R) from (by
          unfold nb088AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088AlphaDummy008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy013 A B C R) ≠ (nb088AlphaDummy020 A B C R) from (by
          unfold
            nb088AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  1)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy023 u A
        B C R) from (by
          unfold
            nb088AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy019 A B C R) from (by
          unfold
            nb088AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy022 u
        A B C R) from (by
          unfold
            nb088AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold
            nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy018
        u A B C R) from (by
          unfold
            nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015
                    u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R)
        from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A
        B C R) ≠ (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠ (nb088AlphaDummy033 A B C R)
        from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy033 A B C R) from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy013 A B C R) from (by
          unfold nb088AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy015 u A B C R) from (by
          unfold nb088AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy014 A B C R) from (by
          unfold nb088AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  1)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy016 u A B C R) from (by
          unfold nb088AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy039 A B C R) from (by
          unfold nb088AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy040 u A B C R) from (by
          unfold nb088AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy006 A B C R) ≠
        (nb088AlphaDummy037 A B C R) from (by
          unfold nb088AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088AlphaDummy008 u A B C R) ≠
        (nb088AlphaDummy038 u A B C R) from (by
          unfold nb088AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088AlphaDummy008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy013 A B C R) ≠ (nb088AlphaDummy020 A B C R) from (by
          unfold
            nb088AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  1)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy023 u A
        B C R) from (by
          unfold
            nb088AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  1)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy019 A B C R) from (by
          unfold
            nb088AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy022 u
        A B C R) from (by
          unfold
            nb088AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold
            nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014
                    A B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠ (nb088AlphaDummy018
        u A B C R) from (by
          unfold
            nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015
                    u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠ (nb088AlphaDummy027 A B C R)
        from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy027 A B C R) from (by
          unfold
            nb088AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy028 u A B C
        R) from (by
          unfold
            nb088AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy025 A B C R) from (by
          unfold
            nb088AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy026 u A B C
        R) from (by
          unfold
            nb088AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy021 A B C R), (nb088AlphaDummy024 u A B C R)),
        ((nb088AlphaDummy020 A B C R), (nb088AlphaDummy023 u A B C R)),
        ((nb088AlphaDummy019 A B C R), (nb088AlphaDummy022 u A B C R)),
        ((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088AlphaDummy013 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy020 A
        B C R) ≠ (nb088AlphaDummy031 A B C R) from (by
          unfold
            nb088AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy032 u A B C
        R) from (by
          unfold
            nb088AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy020 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy023 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088AlphaDummy013
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088AlphaDummy015 u A B C R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠ (nb088AlphaDummy033 A B C R)
        from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy021 A
        B C R) ≠ (nb088AlphaDummy033 A B C R) from (by
          unfold
            nb088AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy034 u A B C
        R) from (by
          unfold
            nb088AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088AlphaDummy021 A B C R) ≠
        (nb088AlphaDummy029 A B C R) from (by
          unfold
            nb088AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088AlphaDummy024 u A B C R) ≠ (nb088AlphaDummy030 u A B C
        R) from (by
          unfold
            nb088AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088AlphaDummy013 A B C R) ≠
        (nb088AlphaDummy017 A B C R) from (by
          unfold nb088AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088AlphaDummy015 u A B C R) ≠
        (nb088AlphaDummy018 u A B C R) from (by
          unfold nb088AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb088AlphaDummy017 A B C R), (nb088AlphaDummy018 u A B C R)),
        ((nb088AlphaDummy013 A B C R), (nb088AlphaDummy015 u A B C R)),
        ((nb088AlphaDummy014 A B C R), (nb088AlphaDummy016 u A B C R)),
        ((nb088AlphaDummy039 A B C R), (nb088AlphaDummy040 u A B C R)),
        ((nb088AlphaDummy037 A B C R), (nb088AlphaDummy038 u A B C R)),
        ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
        ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
        ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
        ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
        ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
        ((nb088AlphaDummy000 A B C R), u), ((nb088AlphaDummy003 A B C R),
        (nb088AlphaDummy004 u A B C R))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed [((nb088AlphaDummy037 A B C R),
                            (nb088AlphaDummy038 u A B C R)),
                          ((nb088AlphaDummy006 A B C R), (nb088AlphaDummy008 u A B C R)),
                          ((nb088AlphaDummy005 A B C R), (nb088AlphaDummy007 u A B C R)),
                          ((nb088AlphaDummy035 A B C R), (nb088AlphaDummy036 u A B C R)),
                          ((nb088AlphaDummy009 A B C R), (nb088AlphaDummy010 u A B C R)),
                          ((nb088AlphaDummy001 A B C R), (nb088AlphaDummy002 u A B C R)),
                          ((nb088AlphaDummy000 A B C R), u),
                          ((nb088AlphaDummy003 A B C R), (nb088AlphaDummy004 u A B C R))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb088SplitAlpha0000 u A B C R))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
