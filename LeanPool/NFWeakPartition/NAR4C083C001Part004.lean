/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C083C001Part003

/-! NF weak partition development: NAR4C083C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb083_split_alpha_0001`. -/
@[expose]
noncomputable def nb083SplitAlpha0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) (dv_B_b : b ∉ B.fv)
    (dv_B_c : c ∉ B.fv) (dv_C_b : b ∉ C.fv) (dv_C_c : c ∉ C.fv) (dv_R_b : b ∉ R.fv)
    (dv_R_c : c ∉ R.fv) (dv_b_c : b ≠ c) :
    TAlphaWff [((nb083AlphaDummy000 A B C R), b)]
      (Wff.imp (Wff.classMem (Class.cv (nb083AlphaDummy000 A B C R)) A) (Wff.neg (synWa
            (Wff.classMem (Class.cv (nb083AlphaDummy000 A B C R)) (synCsep2 B C))
            (synWral (nb083AlphaDummy001 A B C R) A (Wff.imp
                (Wff.classMem (Class.cv (nb083AlphaDummy001 A B C R)) (synCsep2 B C))
                (synWbr (Class.cv (nb083AlphaDummy000 A B C R)) R
                  (Class.cv (nb083AlphaDummy001 A B C R))))))))
      (Wff.imp (Wff.classMem (Class.cv b) A) (Wff.neg
          (synWa (Wff.classMem (Class.cv b) (synCsep2 B C)) (synWral c A
              (Wff.imp (Wff.classMem (Class.cv c) (synCsep2 B C))
                (synWbr (Class.cv b) R (Class.cv c))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
      (TAlphaClass.reflOfReflOn [((nb083AlphaDummy000 A B C R), b)] A
        (nb083FocusedRefl0000 A B C R b dv_A_b))) (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.reflOfReflOn [((nb083AlphaDummy000 A B C R), b)]
            (synCsep2 B C) (nb083WppRefl0000 A B C R b dv_B_b dv_C_b))) (TAlphaWff.all
          (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb083AlphaDummy001 A B C R), c),
                  ((nb083AlphaDummy000 A B C R), b)]
                A (nb083FocusedRefl0001 A B C R b c dv_A_b dv_A_c))) (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn [((nb083AlphaDummy001 A B C R), c),
                    ((nb083AlphaDummy000 A B C R), b)] (synCsep2 B C)
                  (nb083WppRefl0001 A B C R b c dv_B_b dv_B_c dv_C_b dv_C_c)))
              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy003 A B C R)
        from (by
          unfold nb083AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  1)))) (show b ≠ (nb083AlphaDummy005 b c) from (by
          unfold nb083AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c) 1)))) (TAlphaVar.there (show
        (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy002 A B C R) from (by
          unfold nb083AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  0)))) (show b ≠ (nb083AlphaDummy004 b c) from (by
          unfold nb083AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy000 A B C R) ≠
        (nb083AlphaDummy008 A B C R) from (by
          unfold nb083AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0004 A B C
                    R)
                  0)))) (show b ≠ (nb083AlphaDummy009 b c) from (by
          unfold nb083AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0005 b c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy000 A B C R) ≠
        (nb083AlphaDummy006 A B C R) from (by
          unfold nb083AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0001 A B
                    C R)
                  0)))) (show b ≠ (nb083AlphaDummy007 b c) from (by
          unfold nb083AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0003 b c)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv)
        (by decide)) dv_b_c (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy003 A B C R) ≠ (nb083AlphaDummy010 A B C R)
        from (by
          unfold nb083AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A
                    B C R)
                  0)))) (show (nb083AlphaDummy005 b c) ≠ (nb083AlphaDummy012 b c) from (by
          unfold nb083AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy003 A B C R) ≠
        (nb083AlphaDummy011 A B C R) from (by
          unfold nb083AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006
                    A B C R)
                  1)))) (show (nb083AlphaDummy005 b c) ≠ (nb083AlphaDummy013 b c) from (by
          unfold nb083AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007
                    b c)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy003 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy005 b c))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy010
        A B C R) ≠ (nb083AlphaDummy017 A B C R) from (by
          unfold
            nb083AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C
                    R)
                  1)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy020 b c) from (by
          unfold
            nb083AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  1)))) (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy016 A B C R) from (by
          unfold
            nb083AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B
                    C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy019 b c) from (by
          unfold
            nb083AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy018 A B C R), (nb083AlphaDummy021 b c)), ((nb083AlphaDummy017
        A B C R), (nb083AlphaDummy020 b c)), ((nb083AlphaDummy016 A B C R),
        (nb083AlphaDummy019 b c)), ((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015
        b c)), ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)), ((nb083AlphaDummy003
        A B C R), (nb083AlphaDummy005 b c)), ((nb083AlphaDummy002 A B C R),
        (nb083AlphaDummy004 b c)), ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009
        b c)), ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synC1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy017 A
        B C R) ≠ (nb083AlphaDummy024 A B C R) from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy018 A
        B C R) ≠ (nb083AlphaDummy024 A B C R) from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠ (nb083AlphaDummy024 A B C R)
        from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy018 A
        B C R) ≠ (nb083AlphaDummy024 A B C R) from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy018 A B C R), (nb083AlphaDummy021 b c)), ((nb083AlphaDummy017
        A B C R), (nb083AlphaDummy020 b c)), ((nb083AlphaDummy016 A B C R),
        (nb083AlphaDummy019 b c)), ((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015
        b c)), ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)), ((nb083AlphaDummy003
        A B C R), (nb083AlphaDummy005 b c)), ((nb083AlphaDummy002 A B C R),
        (nb083AlphaDummy004 b c)), ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009
        b c)), ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy028 A B C R) from (by
          unfold
            nb083AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy029 b c) from (by
          unfold
            nb083AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy017 A
        B C R) ≠ (nb083AlphaDummy028 A B C R) from (by
          unfold
            nb083AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy029 b c) from (by
          unfold
            nb083AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠ (nb083AlphaDummy030 A B C R)
        from (by
          unfold
            nb083AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy031 b c) from (by
          unfold
            nb083AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy018 A
        B C R) ≠ (nb083AlphaDummy030 A B C R) from (by
          unfold
            nb083AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy031 b c) from (by
          unfold
            nb083AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015 b c)),
        ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)),
        ((nb083AlphaDummy003 A B C R), (nb083AlphaDummy005 b c)),
        ((nb083AlphaDummy002 A B C R), (nb083AlphaDummy004 b c)),
        ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009 b c)),
        ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synCnnc)
        (by
          simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083AlphaDummy010 A B C R) ≠ (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015 b c)),
        ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)),
        ((nb083AlphaDummy003 A B C R), (nb083AlphaDummy005 b c)),
        ((nb083AlphaDummy002 A B C R), (nb083AlphaDummy004 b c)),
        ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009 b c)),
        ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synCnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy003 A B C R)
        from (by
          unfold nb083AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  1)))) (show b ≠ (nb083AlphaDummy005 b c) from (by
          unfold nb083AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c) 1)))) (TAlphaVar.there (show
        (nb083AlphaDummy000 A B C R) ≠ (nb083AlphaDummy002 A B C R) from (by
          unfold nb083AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  0)))) (show b ≠ (nb083AlphaDummy004 b c) from (by
          unfold nb083AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy000 A B C R) ≠
        (nb083AlphaDummy008 A B C R) from (by
          unfold nb083AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0004 A B C
                    R)
                  0)))) (show b ≠ (nb083AlphaDummy009 b c) from (by
          unfold nb083AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0005 b c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy000 A B C R) ≠
        (nb083AlphaDummy006 A B C R) from (by
          unfold nb083AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0001 A B
                    C R)
                  0)))) (show b ≠ (nb083AlphaDummy007 b c) from (by
          unfold nb083AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0003 b c)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv)
        (by decide)) dv_b_c (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy000 A B C R))).fv ∪
        ((Class.cv (nb083AlphaDummy001 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy003 A B C R) ≠ (nb083AlphaDummy010 A B C R)
        from (by
          unfold nb083AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A
                    B C R)
                  0)))) (show (nb083AlphaDummy005 b c) ≠ (nb083AlphaDummy012 b c) from (by
          unfold nb083AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy003 A B C R) ≠
        (nb083AlphaDummy011 A B C R) from (by
          unfold nb083AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006
                    A B C R)
                  1)))) (show (nb083AlphaDummy005 b c) ≠ (nb083AlphaDummy013 b c) from (by
          unfold nb083AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007
                    b c)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy003 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy005 b c))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy010
        A B C R) ≠ (nb083AlphaDummy017 A B C R) from (by
          unfold
            nb083AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C
                    R)
                  1)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy020 b c) from (by
          unfold
            nb083AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  1)))) (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy016 A B C R) from (by
          unfold
            nb083AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B
                    C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy019 b c) from (by
          unfold
            nb083AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy018 A B C R), (nb083AlphaDummy021 b c)), ((nb083AlphaDummy017
        A B C R), (nb083AlphaDummy020 b c)), ((nb083AlphaDummy016 A B C R),
        (nb083AlphaDummy019 b c)), ((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015
        b c)), ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)), ((nb083AlphaDummy003
        A B C R), (nb083AlphaDummy005 b c)), ((nb083AlphaDummy002 A B C R),
        (nb083AlphaDummy004 b c)), ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009
        b c)), ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synC1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy017 A
        B C R) ≠ (nb083AlphaDummy024 A B C R) from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy018 A
        B C R) ≠ (nb083AlphaDummy024 A B C R) from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠ (nb083AlphaDummy024 A B C R)
        from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy018 A
        B C R) ≠ (nb083AlphaDummy024 A B C R) from (by
          unfold
            nb083AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy025 b c) from (by
          unfold
            nb083AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy022 A B C R) from (by
          unfold
            nb083AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy023 b c) from (by
          unfold
            nb083AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy018 A B C R), (nb083AlphaDummy021 b c)), ((nb083AlphaDummy017
        A B C R), (nb083AlphaDummy020 b c)), ((nb083AlphaDummy016 A B C R),
        (nb083AlphaDummy019 b c)), ((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015
        b c)), ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)), ((nb083AlphaDummy003
        A B C R), (nb083AlphaDummy005 b c)), ((nb083AlphaDummy002 A B C R),
        (nb083AlphaDummy004 b c)), ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009
        b c)), ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083AlphaDummy010 A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy028 A B C R) from (by
          unfold
            nb083AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy029 b c) from (by
          unfold
            nb083AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy017 A
        B C R) ≠ (nb083AlphaDummy028 A B C R) from (by
          unfold
            nb083AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy029 b c) from (by
          unfold
            nb083AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy017 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy020 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083AlphaDummy010
        A B C R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083AlphaDummy012 b c))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠ (nb083AlphaDummy030 A B C R)
        from (by
          unfold
            nb083AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy031 b c) from (by
          unfold
            nb083AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy018 A
        B C R) ≠ (nb083AlphaDummy030 A B C R) from (by
          unfold
            nb083AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy031 b c) from (by
          unfold
            nb083AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083AlphaDummy018 A B C R) ≠
        (nb083AlphaDummy026 A B C R) from (by
          unfold
            nb083AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083AlphaDummy021 b c) ≠ (nb083AlphaDummy027 b c) from (by
          unfold
            nb083AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015 b c)),
        ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)),
        ((nb083AlphaDummy003 A B C R), (nb083AlphaDummy005 b c)),
        ((nb083AlphaDummy002 A B C R), (nb083AlphaDummy004 b c)),
        ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009 b c)),
        ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synCnnc)
        (by
          simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083AlphaDummy010 A B C R) ≠ (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083AlphaDummy010 A B C R) ≠
        (nb083AlphaDummy014 A B C R) from (by
          unfold
            nb083AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083AlphaDummy012 b c) ≠ (nb083AlphaDummy015 b c) from (by
          unfold
            nb083AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb083AlphaDummy014 A B C R), (nb083AlphaDummy015 b c)),
        ((nb083AlphaDummy010 A B C R), (nb083AlphaDummy012 b c)),
        ((nb083AlphaDummy011 A B C R), (nb083AlphaDummy013 b c)),
        ((nb083AlphaDummy003 A B C R), (nb083AlphaDummy005 b c)),
        ((nb083AlphaDummy002 A B C R), (nb083AlphaDummy004 b c)),
        ((nb083AlphaDummy008 A B C R), (nb083AlphaDummy009 b c)),
        ((nb083AlphaDummy006 A B C R), (nb083AlphaDummy007 b c)),
        ((nb083AlphaDummy001 A B C R), c), ((nb083AlphaDummy000 A B C R), b)] (synCnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb083SplitAlpha0000 A B C R b c))))))))
                (TAlphaClass.reflOfReflOn [((nb083AlphaDummy001 A B C R), c),
                    ((nb083AlphaDummy000 A B C R), b)]
                  R (nb083FocusedRefl0002 A B C R b c dv_R_b dv_R_c)))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_fpiv`. -/
@[expose]
noncomputable def nominalDfFpiv (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv)
    (__dv_B_C : Disjoint B.fv C.fv) (__dv_B_R : Disjoint B.fv R.fv) (dv_B_b : b ∉ B.fv)
    (dv_B_c : c ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv) (dv_C_b : b ∉ C.fv)
    (dv_C_c : c ∉ C.fv) (dv_R_b : b ∉ R.fv) (dv_R_c : c ∉ R.fv) (dv_b_c : b ≠ c) :
    Nominal.NPrf
      (.classEq (synCfpiv R A B C) (synCrab b A (synWa (.classMem (.cv b) (synCsep2 B C))
            (synWral c A (.imp (.classMem (.cv c) (synCsep2 B C))
                (synWbr (.cv b) R (.cv c))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.neg
          (nb083SplitAlpha0001 A B C R b c dv_A_b dv_A_c dv_B_b dv_B_c dv_C_b dv_C_c
            dv_R_b dv_R_c dv_b_c)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
