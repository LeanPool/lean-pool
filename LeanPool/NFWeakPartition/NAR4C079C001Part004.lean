/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C079C001Block001

/-! NF weak partition development: NAR4C079C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb079_split_alpha_0000`. -/
@[expose]
noncomputable def nb079SplitAlpha0000 (x : Var) (y : Var) (z : Var) (A : Class) :
    TAlphaWff
      [((nb079AlphaDummy053 A), (nb079AlphaDummy054 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)]
      (Wff.imp (Wff.classMem (Class.cv (nb079AlphaDummy053 A))
          (Class.cab (nb079AlphaDummy023 A)
            (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb079AlphaDummy053 A))
            (Class.cab (nb079AlphaDummy023 A)
              (synWrex (nb079AlphaDummy024 A) (Class.cv (nb079AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb079AlphaDummy023 A))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy024 A)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb079AlphaDummy054 x y))
          (Class.cab (nb079AlphaDummy025 x y)
            (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb079AlphaDummy054 x y))
            (Class.cab (nb079AlphaDummy025 x y)
              (synWrex (nb079AlphaDummy026 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb079AlphaDummy025 x y))
                  (synCun (synCphi (Class.cv (nb079AlphaDummy026 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy024 A) from (by
                      unfold nb079AlphaDummy024;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))))
                  (show y ≠ (nb079AlphaDummy026 x y) from (by
                      unfold nb079AlphaDummy026;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb079_support_mem_0058 x y) 1)))) (TAlphaVar.there
                    (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy023 A) from (by
                        unfold nb079AlphaDummy023;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb079_support_mem_0056 A) 0))))
                    (show y ≠ (nb079AlphaDummy025 x y) from (by
                        unfold nb079AlphaDummy025;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))))
                    (TAlphaVar.there
                      (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy053 A) from (by
                          unfold nb079AlphaDummy053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb079_support_mem_0060 A) 0))))
                      (show y ≠ (nb079AlphaDummy054 x y) from (by
                          unfold nb079AlphaDummy054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb079_support_mem_0061 x y) 0))))
                      (TAlphaVar.there
                        (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy027 A) from (by
                            unfold nb079AlphaDummy027;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb079_support_mem_0057 A) 0))))
                        (show y ≠ (nb079AlphaDummy028 x y) from (by
                            unfold nb079AlphaDummy028;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb079_support_mem_0059 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb079AlphaDummy000 A))).fv ∪
                      ((Class.cv (nb079AlphaDummy001 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy031 A) from (by
          unfold nb079AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy033 x y) from (by
          unfold nb079AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy032 A) from (by
          unfold nb079AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy034 x y) from (by
          unfold nb079AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 1)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy057 A) from (by
          unfold nb079AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0064 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy058 x y) from (by
          unfold nb079AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy055 A) from (by
          unfold nb079AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0062 A)
                  0)))) (show (nb079AlphaDummy026 x y) ≠ (nb079AlphaDummy056 x y) from (by
          unfold nb079AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb079AlphaDummy024 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy026 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy031 A) ≠ (nb079AlphaDummy038 A) from (by
          unfold
            nb079AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy041 x y) from (by
          unfold
            nb079AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy037 A) from (by
          unfold
            nb079AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy040 x y) from (by
          unfold
            nb079AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold
            nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold
            nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038
        A) ≠ (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy031 A) from (by
          unfold nb079AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy033 x y) from (by
          unfold nb079AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy032 A) from (by
          unfold nb079AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy034 x y) from (by
          unfold nb079AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 1)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy057 A) from (by
          unfold nb079AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0064 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy058 x y) from (by
          unfold nb079AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy055 A) from (by
          unfold nb079AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0062 A)
                  0)))) (show (nb079AlphaDummy026 x y) ≠ (nb079AlphaDummy056 x y) from (by
          unfold nb079AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb079AlphaDummy024 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy026 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy031 A) ≠ (nb079AlphaDummy038 A) from (by
          unfold
            nb079AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy041 x y) from (by
          unfold
            nb079AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy037 A) from (by
          unfold
            nb079AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy040 x y) from (by
          unfold
            nb079AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold
            nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold
            nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038
        A) ≠ (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb079AlphaDummy055 A), (nb079AlphaDummy056 x y)),
                          ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
                          ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)),
                          ((nb079AlphaDummy053 A), (nb079AlphaDummy054 x y)),
                          ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
                          ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
                          ((nb079AlphaDummy002 A), z)] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy024 A) from (by
                        unfold nb079AlphaDummy024;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb079_support_mem_0056 A) 1))))
                    (show y ≠ (nb079AlphaDummy026 x y) from (by
                        unfold nb079AlphaDummy026;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))))
                    (TAlphaVar.there
                      (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy023 A) from (by
                          unfold nb079AlphaDummy023;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb079_support_mem_0056 A) 0))))
                      (show y ≠ (nb079AlphaDummy025 x y) from (by
                          unfold nb079AlphaDummy025;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))))
                      (TAlphaVar.there
                        (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy053 A) from (by
                            unfold nb079AlphaDummy053;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb079_support_mem_0060 A) 0))))
                        (show y ≠ (nb079AlphaDummy054 x y) from (by
                            unfold nb079AlphaDummy054;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb079_support_mem_0061 x y) 0))))
                        (TAlphaVar.there
                          (show (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy027 A) from (by
                              unfold nb079AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb079_support_mem_0057 A) 0))))
                          (show y ≠ (nb079AlphaDummy028 x y) from (by
                              unfold nb079AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb079_support_mem_0059 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb079AlphaDummy000 A))).fv ∪
                        ((Class.cv (nb079AlphaDummy001 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy031 A) from (by
          unfold nb079AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy033 x y) from (by
          unfold nb079AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy032 A) from (by
          unfold nb079AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy034 x y) from (by
          unfold nb079AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy057 A) from (by
          unfold nb079AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0064 A)
                  0)))) (show (nb079AlphaDummy026 x y) ≠ (nb079AlphaDummy058 x y) from (by
          unfold nb079AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy055 A) from (by
          unfold nb079AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0062 A)
                  0)))) (show (nb079AlphaDummy026 x y) ≠ (nb079AlphaDummy056 x y) from (by
          unfold nb079AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy024 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy026 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031
        A) ≠ (nb079AlphaDummy038 A) from (by
          unfold
            nb079AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy041 x y) from (by
          unfold
            nb079AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy037 A) from (by
          unfold
            nb079AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy040 x y) from (by
          unfold
            nb079AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold
            nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold
            nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038
        A) ≠ (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy031 A) from (by
          unfold nb079AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy033 x y) from (by
          unfold nb079AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy032 A) from (by
          unfold nb079AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy034 x y) from (by
          unfold nb079AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy057 A) from (by
          unfold nb079AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0064 A)
                  0)))) (show (nb079AlphaDummy026 x y) ≠ (nb079AlphaDummy058 x y) from (by
          unfold nb079AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠
        (nb079AlphaDummy055 A) from (by
          unfold nb079AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0062 A)
                  0)))) (show (nb079AlphaDummy026 x y) ≠ (nb079AlphaDummy056 x y) from (by
          unfold nb079AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy024 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy026 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031
        A) ≠ (nb079AlphaDummy038 A) from (by
          unfold
            nb079AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy041 x y) from (by
          unfold
            nb079AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy037 A) from (by
          unfold
            nb079AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy040 x y) from (by
          unfold
            nb079AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold
            nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold
            nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002
        A), z)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038
        A) ≠ (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy057 A), (nb079AlphaDummy058 x y)), ((nb079AlphaDummy055 A),
        (nb079AlphaDummy056 x y)), ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
        ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)), ((nb079AlphaDummy053 A),
        (nb079AlphaDummy054 x y)), ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb079AlphaDummy055 A), (nb079AlphaDummy056 x y)),
                            ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)),
                            ((nb079AlphaDummy023 A), (nb079AlphaDummy025 x y)),
                            ((nb079AlphaDummy053 A), (nb079AlphaDummy054 x y)),
                            ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
                            ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
                            ((nb079AlphaDummy002 A), z)] (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb079_focused_notmem_0000 (A : Class) : (nb079AlphaDummy001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem nb079_focused_notmem_0001 (A : Class) : (nb079AlphaDummy000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem nb079_focused_notmem_0002 (A : Class) : (nb079AlphaDummy002 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => hu)

theorem nb079_compact_envfresh_0007 (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) :
    TEnvFresh
      [((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb079AlphaDummy001 A) y (nb079_focused_notmem_0000 A) dv_A_y
      (TEnvFresh.consFresh (nb079AlphaDummy000 A) x (nb079_focused_notmem_0001 A) dv_A_x
        (TEnvFresh.consFresh (nb079AlphaDummy002 A) z (nb079_focused_notmem_0002 A)
          dv_A_z (TEnvFresh.nil A.fv))))

/-- Checked nominal proof certificate identified upstream as `nb079_focused_refl_0000`. -/
@[expose]
noncomputable def nb079FocusedRefl0000 (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) :
    TReflOn
      [((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)]
      A.fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0007 x y z A dv_A_x dv_A_y dv_A_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
