/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C087C001Block001

/-! NF weak partition development: NAR4C087C001Part003. -/


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

/-- Checked nominal proof certificate identified upstream as `nb087_split_alpha_0000`. -/
@[expose]
noncomputable def nb087SplitAlpha0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) :
    TAlphaWff
      [((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)]
      (Wff.imp (Wff.classMem (Class.cv (nb087AlphaDummy033 A B C R))
          (Class.cab (nb087AlphaDummy001 A B C R) (synWrex (nb087AlphaDummy002 A B C R) C
              (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb087AlphaDummy033 A B C R))
            (Class.cab (nb087AlphaDummy001 A B C R)
              (synWrex (nb087AlphaDummy002 A B C R) C
                (Wff.classEq (Class.cv (nb087AlphaDummy001 A B C R))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy002 A B C R)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb087AlphaDummy034 C d))
          (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
              (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb087AlphaDummy034 C d))
            (Class.cab (nb087AlphaDummy003 C d) (synWrex (nb087AlphaDummy004 C d) C
                (Wff.classEq (Class.cv (nb087AlphaDummy003 C d))
                  (synCun (synCphi (Class.cv (nb087AlphaDummy004 C d)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn
                [((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
                  ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
                  ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
                  ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
                  ((nb087AlphaDummy000 A B C R), d)]
                C (nb087FocusedRefl0000 A B C R d dv_C_d))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv)
                    (by decide))
                  (freshVar_injective (((synCsn (Class.cv d))).fv ∪ (C).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy011 A B C R) from (by
          unfold nb087AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy013 C d) from (by
          unfold nb087AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy012 A B C R) from (by
          unfold nb087AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy014 C d) from (by
          unfold nb087AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 1)))) (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy037 A B C R) from (by
          unfold nb087AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy038 C d) from (by
          unfold nb087AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy035 A B C R) from (by
          unfold nb087AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B C
                    R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy036 C d) from (by
          unfold nb087AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087AlphaDummy002 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087AlphaDummy004 C d))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy011 A B C R) ≠ (nb087AlphaDummy018 A B C R) from (by
          unfold
            nb087AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy021 C d) from (by
          unfold
            nb087AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy017 A B C R) from (by
          unfold
            nb087AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy020 C d) from (by
          unfold
            nb087AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold
            nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold
            nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)),
        ((nb087AlphaDummy018 A B C R), (nb087AlphaDummy021 C d)),
        ((nb087AlphaDummy017 A B C R), (nb087AlphaDummy020 C d)),
        ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R)
        from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)), ((nb087AlphaDummy018
        A B C R), (nb087AlphaDummy021 C d)), ((nb087AlphaDummy017 A B C R),
        (nb087AlphaDummy020 C d)), ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016
        C d)), ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy037
        A B C R), (nb087AlphaDummy038 C d)), ((nb087AlphaDummy035 A B C R),
        (nb087AlphaDummy036 C d)), ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004
        C d)), ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)), ((nb087AlphaDummy005
        A B C R), (nb087AlphaDummy006 C d)), ((nb087AlphaDummy000 A B C R), d)] (synC0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A
        B C R) ≠ (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠ (nb087AlphaDummy031 A B C R)
        from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy031 A B C R) from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A B
                    C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy011 A B C R) from (by
          unfold nb087AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy013 C d) from (by
          unfold nb087AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy012 A B C R) from (by
          unfold nb087AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy014 C d) from (by
          unfold nb087AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 1)))) (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy037 A B C R) from (by
          unfold nb087AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy038 C d) from (by
          unfold nb087AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy035 A B C R) from (by
          unfold nb087AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B C
                    R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy036 C d) from (by
          unfold nb087AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087AlphaDummy002 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087AlphaDummy004 C d))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy011 A B C R) ≠ (nb087AlphaDummy018 A B C R) from (by
          unfold
            nb087AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy021 C d) from (by
          unfold
            nb087AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy017 A B C R) from (by
          unfold
            nb087AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy020 C d) from (by
          unfold
            nb087AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold
            nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold
            nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)),
        ((nb087AlphaDummy018 A B C R), (nb087AlphaDummy021 C d)),
        ((nb087AlphaDummy017 A B C R), (nb087AlphaDummy020 C d)),
        ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R)
        from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)), ((nb087AlphaDummy018
        A B C R), (nb087AlphaDummy021 C d)), ((nb087AlphaDummy017 A B C R),
        (nb087AlphaDummy020 C d)), ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016
        C d)), ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy037
        A B C R), (nb087AlphaDummy038 C d)), ((nb087AlphaDummy035 A B C R),
        (nb087AlphaDummy036 C d)), ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004
        C d)), ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)), ((nb087AlphaDummy005
        A B C R), (nb087AlphaDummy006 C d)), ((nb087AlphaDummy000 A B C R), d)] (synC0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A
        B C R) ≠ (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠ (nb087AlphaDummy031 A B C R)
        from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy031 A B C R) from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A B
                    C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
                          ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
                          ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
                          ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
                          ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
                          ((nb087AlphaDummy000 A B C R), d)] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn
                  [((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
                    ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
                    ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
                    ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
                    ((nb087AlphaDummy000 A B C R), d)]
                  C (nb087FocusedRefl0000 A B C R d dv_C_d))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((synCsn (Class.cv (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv)
                      (by decide)) (freshVar_injective (((synCsn (Class.cv d))).fv ∪ (C).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy011 A B C R)
        from (by
          unfold nb087AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy013 C d) from (by
          unfold nb087AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy012 A B C R) from (by
          unfold nb087AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy014 C d) from (by
          unfold nb087AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy037 A B C R) from (by
          unfold nb087AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C
                    R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy038 C d) from (by
          unfold nb087AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy035 A B C R) from (by
          unfold nb087AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B
                    C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy036 C d) from (by
          unfold nb087AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy011 A B C R) ≠ (nb087AlphaDummy018 A B C R) from (by
          unfold
            nb087AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy021 C d) from (by
          unfold
            nb087AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy017 A B C R) from (by
          unfold
            nb087AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy020 C d) from (by
          unfold
            nb087AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold
            nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold
            nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)), ((nb087AlphaDummy018
        A B C R), (nb087AlphaDummy021 C d)), ((nb087AlphaDummy017 A B C R),
        (nb087AlphaDummy020 C d)), ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016
        C d)), ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy037
        A B C R), (nb087AlphaDummy038 C d)), ((nb087AlphaDummy035 A B C R),
        (nb087AlphaDummy036 C d)), ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004
        C d)), ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)), ((nb087AlphaDummy005
        A B C R), (nb087AlphaDummy006 C d)), ((nb087AlphaDummy000 A B C R), d)] (synC1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R)
        from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)), ((nb087AlphaDummy018
        A B C R), (nb087AlphaDummy021 C d)), ((nb087AlphaDummy017 A B C R),
        (nb087AlphaDummy020 C d)), ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016
        C d)), ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy037
        A B C R), (nb087AlphaDummy038 C d)), ((nb087AlphaDummy035 A B C R),
        (nb087AlphaDummy036 C d)), ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004
        C d)), ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)), ((nb087AlphaDummy005
        A B C R), (nb087AlphaDummy006 C d)), ((nb087AlphaDummy000 A B C R), d)] (synC0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A
        B C R) ≠ (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠ (nb087AlphaDummy031 A B C R)
        from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy031 A B C R) from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy011 A B C R)
        from (by
          unfold nb087AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy013 C d) from (by
          unfold nb087AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy012 A B C R) from (by
          unfold nb087AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy014 C d) from (by
          unfold nb087AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy037 A B C R) from (by
          unfold nb087AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C
                    R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy038 C d) from (by
          unfold nb087AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy035 A B C R) from (by
          unfold nb087AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B
                    C R)
                  0)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy036 C d) from (by
          unfold nb087AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy011 A B C R) ≠ (nb087AlphaDummy018 A B C R) from (by
          unfold
            nb087AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy021 C d) from (by
          unfold
            nb087AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy017 A B C R) from (by
          unfold
            nb087AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy020 C d) from (by
          unfold
            nb087AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold
            nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold
            nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)), ((nb087AlphaDummy018
        A B C R), (nb087AlphaDummy021 C d)), ((nb087AlphaDummy017 A B C R),
        (nb087AlphaDummy020 C d)), ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016
        C d)), ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy037
        A B C R), (nb087AlphaDummy038 C d)), ((nb087AlphaDummy035 A B C R),
        (nb087AlphaDummy036 C d)), ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004
        C d)), ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)), ((nb087AlphaDummy005
        A B C R), (nb087AlphaDummy006 C d)), ((nb087AlphaDummy000 A B C R), d)] (synC1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠ (nb087AlphaDummy025 A B C R)
        from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy025 A B C R) from (by
          unfold
            nb087AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy026 C d) from (by
          unfold
            nb087AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy023 A B C R) from (by
          unfold
            nb087AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy024 C d) from (by
          unfold
            nb087AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy019 A B C R), (nb087AlphaDummy022 C d)), ((nb087AlphaDummy018
        A B C R), (nb087AlphaDummy021 C d)), ((nb087AlphaDummy017 A B C R),
        (nb087AlphaDummy020 C d)), ((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016
        C d)), ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy037
        A B C R), (nb087AlphaDummy038 C d)), ((nb087AlphaDummy035 A B C R),
        (nb087AlphaDummy036 C d)), ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004
        C d)), ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)), ((nb087AlphaDummy005
        A B C R), (nb087AlphaDummy006 C d)), ((nb087AlphaDummy000 A B C R), d)] (synC0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087AlphaDummy011 A B C R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087AlphaDummy013 C d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy018 A
        B C R) ≠ (nb087AlphaDummy029 A B C R) from (by
          unfold
            nb087AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy030 C d) from (by
          unfold
            nb087AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy018 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy021 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy011
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy013 C d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠ (nb087AlphaDummy031 A B C R)
        from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy019 A
        B C R) ≠ (nb087AlphaDummy031 A B C R) from (by
          unfold
            nb087AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy032 C d) from (by
          unfold
            nb087AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy019 A B C R) ≠
        (nb087AlphaDummy027 A B C R) from (by
          unfold
            nb087AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087AlphaDummy022 C d) ≠ (nb087AlphaDummy028 C d) from (by
          unfold
            nb087AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A B C R) ≠
        (nb087AlphaDummy015 A B C R) from (by
          unfold nb087AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087AlphaDummy013 C d) ≠ (nb087AlphaDummy016 C d) from (by
          unfold nb087AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb087AlphaDummy015 A B C R), (nb087AlphaDummy016 C d)),
        ((nb087AlphaDummy011 A B C R), (nb087AlphaDummy013 C d)),
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)),
        ((nb087AlphaDummy037 A B C R), (nb087AlphaDummy038 C d)),
        ((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb087AlphaDummy035 A B C R), (nb087AlphaDummy036 C d)),
                            ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
                            ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
                            ((nb087AlphaDummy033 A B C R), (nb087AlphaDummy034 C d)),
                            ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
                            ((nb087AlphaDummy000 A B C R), d)]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb087_focused_notmem_0009 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb087_focused_notmem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb087_focused_notmem_0011 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb087_wpp_notmem_0090 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087AlphaDummy000 A B C R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb087AlphaDummy000, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb087_focused_notmem_0009 A B C R) (nb087_focused_notmem_0010 A B C R))
      (nb087_focused_notmem_0011 A B C R))

theorem nb087_wpp_notmem_0091 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    d ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_d dv_B_d) dv_R_d)

theorem nb087_compact_envfresh_0008 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    TEnvFresh [((nb087AlphaDummy000 A B C R), d)] ((synCfdrowrel R A B)).fv := by
  exact
    (TEnvFresh.consFresh (nb087AlphaDummy000 A B C R) d (nb087_wpp_notmem_0090 A B C R)
      (nb087_wpp_notmem_0091 A B R d dv_A_d dv_B_d dv_R_d)
      (TEnvFresh.nil ((synCfdrowrel R A B)).fv))

/-- Checked nominal proof certificate identified upstream as `nb087_wpp_refl_0007`. -/
@[expose]
noncomputable def nb087WppRefl0007 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    TReflOn [((nb087AlphaDummy000 A B C R), d)] ((synCfdrowrel R A B)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0008 A B C R d dv_A_d dv_B_d dv_R_d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
