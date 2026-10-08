/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C087C001Part003

/-! NF weak partition development: NAR4C087C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_fdrowfib`. -/
@[expose]
noncomputable def nominalDfFdrowfib (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (__dv_B_C : Disjoint B.fv C.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv)
    (dv_C_d : d ∉ C.fv) (dv_R_d : d ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synCfdrowfib R A B C)
        (.cab d (.classMem (synCop (synCsn (.cv d)) C) (synCfdrowrel R A B)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy009 A B C R) from (by
          unfold nb087AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0006 A B C R)
                  0)))) (show d ≠ (nb087AlphaDummy010 d) from (by
          unfold nb087AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0007 d) 0)))) (TAlphaVar.there (show
        (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy002 A B C R) from (by
          unfold nb087AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  1)))) (show d ≠ (nb087AlphaDummy004 C d) from (by
          unfold nb087AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d) 1)))) (TAlphaVar.there (show
        (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy001 A B C R) from (by
          unfold nb087AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  0)))) (show d ≠ (nb087AlphaDummy003 C d) from (by
          unfold nb087AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy000 A B C R) ≠
        (nb087AlphaDummy007 A B C R) from (by
          unfold nb087AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0004 A B C
                    R)
                  0)))) (show d ≠ (nb087AlphaDummy008 C d) from (by
          unfold nb087AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0005 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy000 A B C R) ≠
        (nb087AlphaDummy005 A B C R) from (by
          unfold nb087AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0001 A B
                    C R)
                  0)))) (show d ≠ (nb087AlphaDummy006 C d) from (by
          unfold nb087AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0003 C d)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                    (TAlphaVar.there (freshVar_injective (((synCsn (Class.cv
        (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) (by decide)) (freshVar_injective
                                        (((synCsn (Class.cv d))).fv ∪ (C).fv) (by decide))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy011 A B C R) from (by
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
                  (nb087_support_mem_0009 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy012 A B C R) from (by
          unfold nb087AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C
                    R)
                  1)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy014 C d) from (by
          unfold nb087AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A
        B C R) ≠ (nb087AlphaDummy018 A B C R) from (by
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
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy002
        A B C R), (nb087AlphaDummy004 C d)), ((nb087AlphaDummy001 A B C R),
        (nb087AlphaDummy003 C d)), ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008
        C d)), ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synC1c) (by
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
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy002
        A B C R), (nb087AlphaDummy004 C d)), ((nb087AlphaDummy001 A B C R),
        (nb087AlphaDummy003 C d)), ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008
        C d)), ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synC0) (by
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
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008 C d)),
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
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy009 A B C R) from (by
          unfold nb087AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0006 A B C R)
                  0)))) (show d ≠ (nb087AlphaDummy010 d) from (by
          unfold nb087AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0007 d) 0)))) (TAlphaVar.there (show
        (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy002 A B C R) from (by
          unfold nb087AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  1)))) (show d ≠ (nb087AlphaDummy004 C d) from (by
          unfold nb087AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d) 1)))) (TAlphaVar.there (show
        (nb087AlphaDummy000 A B C R) ≠ (nb087AlphaDummy001 A B C R) from (by
          unfold nb087AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  0)))) (show d ≠ (nb087AlphaDummy003 C d) from (by
          unfold nb087AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy000 A B C R) ≠
        (nb087AlphaDummy007 A B C R) from (by
          unfold nb087AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0004 A B C
                    R)
                  0)))) (show d ≠ (nb087AlphaDummy008 C d) from (by
          unfold nb087AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0005 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy000 A B C R) ≠
        (nb087AlphaDummy005 A B C R) from (by
          unfold nb087AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0001 A B
                    C R)
                  0)))) (show d ≠ (nb087AlphaDummy006 C d) from (by
          unfold nb087AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0003 C d)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                    (TAlphaVar.there (freshVar_injective (((synCsn (Class.cv
        (nb087AlphaDummy000 A B C R)))).fv ∪ (C).fv) (by decide)) (freshVar_injective
                                        (((synCsn (Class.cv d))).fv ∪ (C).fv) (by decide))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087AlphaDummy002 A B C R) ≠ (nb087AlphaDummy011 A B C R) from (by
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
                  (nb087_support_mem_0009 C d)
                  0)))) (TAlphaVar.there (show (nb087AlphaDummy002 A B C R) ≠
        (nb087AlphaDummy012 A B C R) from (by
          unfold nb087AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C
                    R)
                  1)))) (show (nb087AlphaDummy004 C d) ≠ (nb087AlphaDummy014 C d) from (by
          unfold nb087AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087AlphaDummy002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087AlphaDummy004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087AlphaDummy011 A
        B C R) ≠ (nb087AlphaDummy018 A B C R) from (by
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
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy002
        A B C R), (nb087AlphaDummy004 C d)), ((nb087AlphaDummy001 A B C R),
        (nb087AlphaDummy003 C d)), ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008
        C d)), ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synC1c) (by
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
        ((nb087AlphaDummy012 A B C R), (nb087AlphaDummy014 C d)), ((nb087AlphaDummy002
        A B C R), (nb087AlphaDummy004 C d)), ((nb087AlphaDummy001 A B C R),
        (nb087AlphaDummy003 C d)), ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008
        C d)), ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synC0) (by
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
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008 C d)),
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
        ((nb087AlphaDummy002 A B C R), (nb087AlphaDummy004 C d)),
        ((nb087AlphaDummy001 A B C R), (nb087AlphaDummy003 C d)),
        ((nb087AlphaDummy007 A B C R), (nb087AlphaDummy008 C d)),
        ((nb087AlphaDummy005 A B C R), (nb087AlphaDummy006 C d)),
        ((nb087AlphaDummy000 A B C R), d)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg
                      (TAlphaWff.neg (nb087SplitAlpha0000 A B C R d dv_C_d))))))))
          (TAlphaClass.reflOfReflOn [((nb087AlphaDummy000 A B C R), d)]
            (synCfdrowrel R A B) (nb087WppRefl0007 A B C R d dv_A_d dv_B_d dv_R_d))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
