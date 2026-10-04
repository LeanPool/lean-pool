/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C081C001Block001

/-! NF weak partition development: NAR4C081C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb081_split_alpha_0000`. -/
@[expose]
noncomputable def nb081SplitAlpha0000 (x : Var) (y : Var) (A : Class) :
    TAlphaWff
      [((nb081AlphaDummy034 A), (nb081AlphaDummy035 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
      (Wff.imp (Wff.classMem (Class.cv (nb081AlphaDummy034 A))
          (Class.cab (nb081AlphaDummy004 A)
            (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb081AlphaDummy034 A))
            (Class.cab (nb081AlphaDummy004 A)
              (synWrex (nb081AlphaDummy005 A) (Class.cv (nb081AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb081AlphaDummy004 A))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy005 A)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb081AlphaDummy035 x y))
          (Class.cab (nb081AlphaDummy006 x y)
            (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb081AlphaDummy035 x y))
            (Class.cab (nb081AlphaDummy006 x y)
              (synWrex (nb081AlphaDummy007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081AlphaDummy006 x y))
                  (synCun (synCphi (Class.cv (nb081AlphaDummy007 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy005 A) from (by
                      unfold nb081AlphaDummy005;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
                  (show y ≠ (nb081AlphaDummy007 x y) from (by
                      unfold nb081AlphaDummy007;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb081_support_mem_0034 x y) 1)))) (TAlphaVar.there
                    (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy004 A) from (by
                        unfold nb081AlphaDummy004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
                    (show y ≠ (nb081AlphaDummy006 x y) from (by
                        unfold nb081AlphaDummy006;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
                    (TAlphaVar.there
                      (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy034 A) from (by
                          unfold nb081AlphaDummy034;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0036 A) 0))))
                      (show y ≠ (nb081AlphaDummy035 x y) from (by
                          unfold nb081AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0037 x y) 0))))
                      (TAlphaVar.there
                        (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy008 A) from (by
                            unfold nb081AlphaDummy008;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0033 A) 0))))
                        (show y ≠ (nb081AlphaDummy009 x y) from (by
                            unfold nb081AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0035 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb081AlphaDummy000 A))).fv ∪
                      ((Class.cv (nb081AlphaDummy001 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy012 A) from (by
          unfold nb081AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy014 x y) from (by
          unfold nb081AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy013 A) from (by
          unfold nb081AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy015 x y) from (by
          unfold nb081AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy038 A) from (by
          unfold nb081AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy039 x y) from (by
          unfold nb081AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy036 A) from (by
          unfold nb081AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081AlphaDummy007 x y) ≠ (nb081AlphaDummy037 x y) from (by
          unfold nb081AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb081AlphaDummy005 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy007 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy019 A) from (by
          unfold
            nb081AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy022 x y) from (by
          unfold
            nb081AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy018 A) from (by
          unfold
            nb081AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy021 x y) from (by
          unfold
            nb081AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold
            nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold
            nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019
        A) ≠ (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy012 A) from (by
          unfold nb081AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy014 x y) from (by
          unfold nb081AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy013 A) from (by
          unfold nb081AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy015 x y) from (by
          unfold nb081AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy038 A) from (by
          unfold nb081AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy039 x y) from (by
          unfold nb081AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy036 A) from (by
          unfold nb081AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081AlphaDummy007 x y) ≠ (nb081AlphaDummy037 x y) from (by
          unfold nb081AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb081AlphaDummy005 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy007 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy019 A) from (by
          unfold
            nb081AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy022 x y) from (by
          unfold
            nb081AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy018 A) from (by
          unfold
            nb081AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy021 x y) from (by
          unfold
            nb081AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold
            nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold
            nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019
        A) ≠ (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb081AlphaDummy036 A), (nb081AlphaDummy037 x y)),
                          ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
                          ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)),
                          ((nb081AlphaDummy034 A), (nb081AlphaDummy035 x y)),
                          ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
                          ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
                          ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy005 A) from (by
                        unfold nb081AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
                    (show y ≠ (nb081AlphaDummy007 x y) from (by
                        unfold nb081AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))))
                    (TAlphaVar.there
                      (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy004 A) from (by
                          unfold nb081AlphaDummy004;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
                      (show y ≠ (nb081AlphaDummy006 x y) from (by
                          unfold nb081AlphaDummy006;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
                      (TAlphaVar.there
                        (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy034 A) from (by
                            unfold nb081AlphaDummy034;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0036 A) 0))))
                        (show y ≠ (nb081AlphaDummy035 x y) from (by
                            unfold nb081AlphaDummy035;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0037 x y) 0))))
                        (TAlphaVar.there
                          (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy008 A) from (by
                              unfold nb081AlphaDummy008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb081_support_mem_0033 A) 0))))
                          (show y ≠ (nb081AlphaDummy009 x y) from (by
                              unfold nb081AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb081_support_mem_0035 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb081AlphaDummy000 A))).fv ∪
                        ((Class.cv (nb081AlphaDummy001 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy012 A) from (by
          unfold nb081AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy014 x y) from (by
          unfold nb081AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy013 A) from (by
          unfold nb081AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy015 x y) from (by
          unfold nb081AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy038 A) from (by
          unfold nb081AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A)
                  0)))) (show (nb081AlphaDummy007 x y) ≠ (nb081AlphaDummy039 x y) from (by
          unfold nb081AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy036 A) from (by
          unfold nb081AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081AlphaDummy007 x y) ≠ (nb081AlphaDummy037 x y) from (by
          unfold nb081AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy005 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy007 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012
        A) ≠ (nb081AlphaDummy019 A) from (by
          unfold
            nb081AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy022 x y) from (by
          unfold
            nb081AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy018 A) from (by
          unfold
            nb081AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy021 x y) from (by
          unfold
            nb081AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold
            nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold
            nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019
        A) ≠ (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy012 A) from (by
          unfold nb081AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy014 x y) from (by
          unfold nb081AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy013 A) from (by
          unfold nb081AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy015 x y) from (by
          unfold nb081AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy038 A) from (by
          unfold nb081AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A)
                  0)))) (show (nb081AlphaDummy007 x y) ≠ (nb081AlphaDummy039 x y) from (by
          unfold nb081AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy036 A) from (by
          unfold nb081AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081AlphaDummy007 x y) ≠ (nb081AlphaDummy037 x y) from (by
          unfold nb081AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy005 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy007 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012
        A) ≠ (nb081AlphaDummy019 A) from (by
          unfold
            nb081AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy022 x y) from (by
          unfold
            nb081AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy018 A) from (by
          unfold
            nb081AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy021 x y) from (by
          unfold
            nb081AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold
            nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold
            nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002
        A), (nb081AlphaDummy003 x y A))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019
        A) ≠ (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy038 A), (nb081AlphaDummy039 x y)), ((nb081AlphaDummy036 A),
        (nb081AlphaDummy037 x y)), ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
        ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)), ((nb081AlphaDummy034 A),
        (nb081AlphaDummy035 x y)), ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb081AlphaDummy036 A), (nb081AlphaDummy037 x y)),
                            ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)),
                            ((nb081AlphaDummy004 A), (nb081AlphaDummy006 x y)),
                            ((nb081AlphaDummy034 A), (nb081AlphaDummy035 x y)),
                            ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
                            ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
                            ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb081_focused_notmem_0000 (A : Class) : (nb081AlphaDummy001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem nb081_focused_notmem_0001 (A : Class) : (nb081AlphaDummy000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem nb081_focused_notmem_0002 (A : Class) : (nb081AlphaDummy002 A) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb081AlphaDummy000 A)} : Finset Var) ∪
            ({(nb081AlphaDummy001 A)} : Finset Var) ∪ ((Wff.classMem
              (synCopk (Class.cv (nb081AlphaDummy000 A))
                (Class.cv (nb081AlphaDummy001 A))) A)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_wff_classMem
      (synCopk (Class.cv (nb081AlphaDummy000 A)) (Class.cv (nb081AlphaDummy001 A)))
      A]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb081_focused_notmem_0003 (x : Var) (y : Var) (A : Class) :
    (nb081AlphaDummy003 x y A) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ((Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_wff_classMem (synCopk (Class.cv x) (Class.cv y)) A]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb081_compact_envfresh_0007 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb081AlphaDummy001 A) y (nb081_focused_notmem_0000 A) dv_A_y
      (TEnvFresh.consFresh (nb081AlphaDummy000 A) x (nb081_focused_notmem_0001 A) dv_A_x
        (TEnvFresh.consFresh (nb081AlphaDummy002 A) (nb081AlphaDummy003 x y A)
          (nb081_focused_notmem_0002 A) (nb081_focused_notmem_0003 x y A)
          (TEnvFresh.nil A.fv))))

/-- Checked nominal proof certificate identified upstream as `nb081_focused_refl_0000`. -/
@[expose]
noncomputable def nb081FocusedRefl0000 (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
      A.fv :=
  TEnvFresh.reflOn (nb081_compact_envfresh_0007 x y A dv_A_x dv_A_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
