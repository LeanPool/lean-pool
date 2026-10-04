/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C096M3Part002Stage1


/-! NF weak partition development: NAR4H5C096M3Part002. -/


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

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0000`. -/
@[expose]
noncomputable def nb096SplitAlpha0000 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.neg (Wff.classMem (Class.cv (nb096AlphaDummy035 D R))
          (Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb096AlphaDummy036 D R q))
          (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
              (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy006 D R) from (by
                      unfold nb096AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
                  (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy008 D R q) from (by
                      unfold nb096AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
                  (TAlphaVar.there
                    (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy005 D R) from (by
                        unfold nb096AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
                    (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy007 D R q) from (by
                        unfold nb096AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
                    (TAlphaVar.there
                      (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy035 D R) from (by
                          unfold nb096AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0038 D R) 0))))
                      (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy036 D R q) from
                        (by
                          unfold nb096AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0039 D R q) 0))))
                      (TAlphaVar.there
                        (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy009 D R) from (by
                            unfold nb096AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0035 D R) 0)))) (show
                          (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy010 D R q) from (by
                            unfold nb096AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0037 D R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
                      ((Class.cv (nb096AlphaDummy001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy013 D R) from (by
          unfold nb096AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy015 D R q) from (by
          unfold nb096AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy006 D R) ≠ (nb096AlphaDummy014 D R) from (by
          unfold nb096AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy016 D R q) from (by
          unfold nb096AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy039 D R) from (by
          unfold nb096AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy040 D R q) from
        (by
          unfold nb096AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy037 D R) from (by
          unfold nb096AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy038 D R q) from
        (by
          unfold nb096AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D
        R) ≠ (nb096AlphaDummy020 D R) from (by
          unfold
            nb096AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy023 D R q) from
        (by
          unfold
            nb096AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy019 D R) from (by
          unfold
            nb096AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy022 D R q) from
        (by
          unfold
            nb096AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold
            nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold
            nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D
        R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039 D
        R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D
        R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009 D
        R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from
        (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020
        D R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018
        D R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039
        D R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008
        D R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009
        D R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠ (nb096AlphaDummy033 D R) from
        (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy033 D R) from (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy013 D R) from (by
          unfold nb096AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy015 D R q) from (by
          unfold nb096AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy006 D R) ≠ (nb096AlphaDummy014 D R) from (by
          unfold nb096AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy016 D R q) from (by
          unfold nb096AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy039 D R) from (by
          unfold nb096AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy040 D R q) from
        (by
          unfold nb096AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy037 D R) from (by
          unfold nb096AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy038 D R q) from
        (by
          unfold nb096AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D
        R) ≠ (nb096AlphaDummy020 D R) from (by
          unfold
            nb096AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy023 D R q) from
        (by
          unfold
            nb096AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy019 D R) from (by
          unfold
            nb096AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy022 D R q) from
        (by
          unfold
            nb096AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold
            nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold
            nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D
        R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039 D
        R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D
        R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009 D
        R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from
        (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020
        D R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018
        D R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039
        D R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008
        D R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009
        D R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠ (nb096AlphaDummy033 D R) from
        (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy033 D R) from (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
                          ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
                          ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
                          ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
                          ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
                          ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                          ((nb096AlphaDummy000 D R), q),
                          ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0001`. -/
@[expose]
noncomputable def nb096SplitAlpha0001 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy035 D R))
          (Class.cab (nb096AlphaDummy005 D R)
            (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy035 D R))
            (Class.cab (nb096AlphaDummy005 D R)
              (synWrex (nb096AlphaDummy006 D R) (Class.cv (nb096AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy036 D R q))
          (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
              (Class.cv (nb096AlphaDummy002 D R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy036 D R q))
            (Class.cab (nb096AlphaDummy007 D R q) (synWrex (nb096AlphaDummy008 D R q)
                (Class.cv (nb096AlphaDummy002 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy007 D R q))
                  (synCun (synCphi (Class.cv (nb096AlphaDummy008 D R q)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy006 D R) from (by
                      unfold nb096AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0034 D R) 1))))
                  (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy008 D R q) from (by
                      unfold nb096AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0036 D R q) 1))))
                  (TAlphaVar.there
                    (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy005 D R) from (by
                        unfold nb096AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0034 D R) 0))))
                    (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy007 D R q) from (by
                        unfold nb096AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0036 D R q) 0))))
                    (TAlphaVar.there
                      (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy035 D R) from (by
                          unfold nb096AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0038 D R) 0))))
                      (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy036 D R q) from
                        (by
                          unfold nb096AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0039 D R q) 0))))
                      (TAlphaVar.there
                        (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy009 D R) from (by
                            unfold nb096AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0035 D R) 0)))) (show
                          (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy010 D R q) from (by
                            unfold nb096AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0037 D R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
                      ((Class.cv (nb096AlphaDummy001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv q)).fv ∪ ((Class.cv (nb096AlphaDummy002 D R q))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy013 D R) from (by
          unfold nb096AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy015 D R q) from (by
          unfold nb096AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy006 D R) ≠ (nb096AlphaDummy014 D R) from (by
          unfold nb096AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy016 D R q) from (by
          unfold nb096AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy039 D R) from (by
          unfold nb096AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy040 D R q) from
        (by
          unfold nb096AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy037 D R) from (by
          unfold nb096AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy038 D R q) from
        (by
          unfold nb096AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D
        R) ≠ (nb096AlphaDummy020 D R) from (by
          unfold
            nb096AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy023 D R q) from
        (by
          unfold
            nb096AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy019 D R) from (by
          unfold
            nb096AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy022 D R q) from
        (by
          unfold
            nb096AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold
            nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold
            nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D
        R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039 D
        R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D
        R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009 D
        R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from
        (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020
        D R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018
        D R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039
        D R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008
        D R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009
        D R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠ (nb096AlphaDummy033 D R) from
        (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy033 D R) from (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy013 D R) from (by
          unfold nb096AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy015 D R q) from (by
          unfold nb096AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy006 D R) ≠ (nb096AlphaDummy014 D R) from (by
          unfold nb096AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy016 D R q) from (by
          unfold nb096AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy039 D R) from (by
          unfold nb096AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0042 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy040 D R q) from
        (by
          unfold nb096AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0043 D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy037 D R) from (by
          unfold nb096AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0040 D R)
                  0)))) (show (nb096AlphaDummy008 D R q) ≠ (nb096AlphaDummy038 D R q) from
        (by
          unfold nb096AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0041 D R q)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D
        R) ≠ (nb096AlphaDummy020 D R) from (by
          unfold
            nb096AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy023 D R q) from
        (by
          unfold
            nb096AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy019 D R) from (by
          unfold
            nb096AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy022 D R q) from
        (by
          unfold
            nb096AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold
            nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold
            nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D
        R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039 D
        R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D
        R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009 D
        R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from
        (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020
        D R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018
        D R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy039
        D R), (nb096AlphaDummy040 D R q)), ((nb096AlphaDummy037 D R),
        (nb096AlphaDummy038 D R q)), ((nb096AlphaDummy006 D R), (nb096AlphaDummy008
        D R q)), ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)), ((nb096AlphaDummy009
        D R), (nb096AlphaDummy010 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠ (nb096AlphaDummy033 D R) from
        (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy033 D R) from (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D
                    R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D
                    R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy039 D R), (nb096AlphaDummy040 D R q)),
        ((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb096AlphaDummy037 D R), (nb096AlphaDummy038 D R q)),
                          ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
                          ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
                          ((nb096AlphaDummy035 D R), (nb096AlphaDummy036 D R q)),
                          ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
                          ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                          ((nb096AlphaDummy000 D R), q),
                          ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb096SplitAlpha0000 D R q))


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

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0002`. -/
@[expose]
noncomputable def nb096SplitAlpha0002 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.classEq (Class.cv (nb096AlphaDummy003 D R))
        (synCop (Class.cv (nb096AlphaDummy000 D R)) (Class.cv (nb096AlphaDummy001 D R))))
      (Wff.classEq (Class.cv (nb096AlphaDummy004 D R q))
        (synCop (Class.cv q) (Class.cv (nb096AlphaDummy002 D R q)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb096AlphaDummy001 D R) ≠ (nb096AlphaDummy003 D R) from (by
              unfold nb096AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0002 D R) 0)))))
        (Ne.symm (show (nb096AlphaDummy002 D R q) ≠ (nb096AlphaDummy004 D R q) from (by
              unfold nb096AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0003 D R q) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy003 D R) from (by
                unfold nb096AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0000 D R) 0)))))
          (Ne.symm (show q ≠ (nb096AlphaDummy004 D R q) from (by
                unfold nb096AlphaDummy004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0001 D R q) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
                                    (nb096AlphaDummy006 D R) from (by
                                    unfold nb096AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                            1)))) (show q ≠ (nb096AlphaDummy008 D R q) from
                                  (by
                                    unfold nb096AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0008 D R q)
                                            1)))) (TAlphaVar.there (show
                                    (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy005 D R)
                                    from (by
                                      unfold nb096AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                              0)))) (show q ≠ (nb096AlphaDummy007 D R q) from
                                    (by
                                      unfold nb096AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0008 D R q) 0))))
                                  (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
                                        (nb096AlphaDummy011 D R) from (by
                                        unfold nb096AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0010 D R) 0))))
                                    (show q ≠ (nb096AlphaDummy012 D R q) from (by
                                        unfold nb096AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0011 D R q) 0))))
                                    (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy009 D R) from (by
                                          unfold nb096AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0007 D R) 0))))
                                      (show q ≠ (nb096AlphaDummy010 D R q) from (by
                                          unfold nb096AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0009 D R q) 0))))
                                      (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy001 D R) from (by
          unfold nb096AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004 D R) 0))))
                                        (show q ≠ (nb096AlphaDummy002 D R q) from (by
          unfold nb096AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0005 D R q) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
                                    ((Class.cv (nb096AlphaDummy001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv q)).fv ∪
                                    ((Class.cv (nb096AlphaDummy002 D R q))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy013 D R) from (by
          unfold nb096AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy015 D R q) from (by
          unfold nb096AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy006 D R) ≠ (nb096AlphaDummy014 D R) from (by
          unfold nb096AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy016 D R q) from (by
          unfold nb096AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb096AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy013 D R) ≠ (nb096AlphaDummy020 D R) from (by
          unfold
            nb096AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy023 D R q) from
        (by
          unfold
            nb096AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy019 D R) from (by
          unfold
            nb096AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy022 D R q) from
        (by
          unfold
            nb096AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold
            nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold
            nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R
        q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy006 D
        R), (nb096AlphaDummy008 D R q)), ((nb096AlphaDummy005 D R),
        (nb096AlphaDummy007 D R q)), ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D R
        q)), ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D
        R), q), ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from
        (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D
        R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy006 D
        R), (nb096AlphaDummy008 D R q)), ((nb096AlphaDummy005 D R),
        (nb096AlphaDummy007 D R q)), ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D
        R q)), ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D
        R), q), ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠ (nb096AlphaDummy033 D R) from
        (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy033 D R) from (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy013 D R) ≠ (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
                                    (nb096AlphaDummy006 D R) from (by
                                    unfold nb096AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                            1)))) (show q ≠ (nb096AlphaDummy008 D R q) from
                                  (by
                                    unfold nb096AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0008 D R q)
                                            1)))) (TAlphaVar.there (show
                                    (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy005 D R)
                                    from (by
                                      unfold nb096AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0006 D R)
                                              0)))) (show q ≠ (nb096AlphaDummy007 D R q) from
                                    (by
                                      unfold nb096AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0008 D R q) 0))))
                                  (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
                                        (nb096AlphaDummy011 D R) from (by
                                        unfold nb096AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0010 D R) 0))))
                                    (show q ≠ (nb096AlphaDummy012 D R q) from (by
                                        unfold nb096AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0011 D R q) 0))))
                                    (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy009 D R) from (by
                                          unfold nb096AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0007 D R) 0))))
                                      (show q ≠ (nb096AlphaDummy010 D R q) from (by
                                          unfold nb096AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0009 D R q) 0))))
                                      (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy001 D R) from (by
          unfold nb096AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004 D R) 0))))
                                        (show q ≠ (nb096AlphaDummy002 D R q) from (by
          unfold nb096AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0005 D R q) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb096AlphaDummy000 D R))).fv ∪
                                    ((Class.cv (nb096AlphaDummy001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv q)).fv ∪
                                    ((Class.cv (nb096AlphaDummy002 D R q))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb096AlphaDummy006 D R) ≠
        (nb096AlphaDummy013 D R) from (by
          unfold nb096AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 0)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy015 D R q) from (by
          unfold nb096AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy006 D R) ≠ (nb096AlphaDummy014 D R) from (by
          unfold nb096AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0012 D R) 1)))) (show (nb096AlphaDummy008 D R q) ≠
        (nb096AlphaDummy016 D R q) from (by
          unfold nb096AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0013 D R q) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb096AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy008 D R q))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy013 D R) ≠ (nb096AlphaDummy020 D R) from (by
          unfold
            nb096AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  1)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy023 D R q) from
        (by
          unfold
            nb096AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy019 D R) from (by
          unfold
            nb096AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0016
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy022 D R q) from
        (by
          unfold
            nb096AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0017
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold
            nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014
                    D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold
            nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R
        q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy006 D
        R), (nb096AlphaDummy008 D R q)), ((nb096AlphaDummy005 D R),
        (nb096AlphaDummy007 D R q)), ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D R
        q)), ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D
        R), q), ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠ (nb096AlphaDummy027 D R) from
        (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0020
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0021
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0018
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0019
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy027 D R) from (by
          unfold
            nb096AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0024
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy028 D R q) from
        (by
          unfold
            nb096AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0025
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy025 D R) from (by
          unfold
            nb096AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0022
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy026 D R q) from
        (by
          unfold
            nb096AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0023
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy021 D R), (nb096AlphaDummy024 D R q)), ((nb096AlphaDummy020 D
        R), (nb096AlphaDummy023 D R q)), ((nb096AlphaDummy019 D R),
        (nb096AlphaDummy022 D R q)), ((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D
        R q)), ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)), ((nb096AlphaDummy006 D
        R), (nb096AlphaDummy008 D R q)), ((nb096AlphaDummy005 D R),
        (nb096AlphaDummy007 D R q)), ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D
        R q)), ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D
        R), q), ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy020 D
        R) ≠ (nb096AlphaDummy031 D R) from (by
          unfold
            nb096AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0028
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy032 D R q) from
        (by
          unfold
            nb096AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0029
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy020 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0026
                    D
                    R)
                  0)))) (show (nb096AlphaDummy023 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0027
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy015 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠ (nb096AlphaDummy033 D R) from
        (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy021 D
        R) ≠ (nb096AlphaDummy033 D R) from (by
          unfold
            nb096AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0032
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy034 D R q) from
        (by
          unfold
            nb096AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0033
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy021 D R) ≠
        (nb096AlphaDummy029 D R) from (by
          unfold
            nb096AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0030
                    D
                    R)
                  0)))) (show (nb096AlphaDummy024 D R q) ≠ (nb096AlphaDummy030 D R q) from
        (by
          unfold
            nb096AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0031
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy013 D R) ≠ (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy013 D R) ≠
        (nb096AlphaDummy017 D R) from (by
          unfold nb096AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0014 D R)
                  0)))) (show (nb096AlphaDummy015 D R q) ≠ (nb096AlphaDummy018 D R q) from
        (by
          unfold nb096AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0015 D R
                    q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy017 D R), (nb096AlphaDummy018 D R q)),
        ((nb096AlphaDummy013 D R), (nb096AlphaDummy015 D R q)),
        ((nb096AlphaDummy014 D R), (nb096AlphaDummy016 D R q)),
        ((nb096AlphaDummy006 D R), (nb096AlphaDummy008 D R q)),
        ((nb096AlphaDummy005 D R), (nb096AlphaDummy007 D R q)),
        ((nb096AlphaDummy011 D R), (nb096AlphaDummy012 D R q)),
        ((nb096AlphaDummy009 D R), (nb096AlphaDummy010 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb096SplitAlpha0001 D R q)))))))))

theorem nb096_focused_notmem_0000 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb096AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0106 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb096AlphaDummy001, fv_syn_cpw1] using (nb096_focused_notmem_0000 D R)

theorem nb096_focused_notmem_0001 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0107 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb096AlphaDummy002, fv_syn_cpw1] using (nb096_focused_notmem_0001 D R q)

theorem nb096_focused_notmem_0002 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb096_wpp_notmem_0108 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb096AlphaDummy000, fv_syn_cpw1] using (nb096_focused_notmem_0002 D R)

theorem nb096_wpp_notmem_0109 (D : Class) (q : Var) (dv_D_q : q ∉ D.fv) :
    q ∉ ((synCpw1 (synCpw1 D))).fv := by simpa only [fv_syn_cpw1] using dv_D_q

theorem nb096_focused_notmem_0003 (D : Class) (R : Class) :
    (nb096AlphaDummy003 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
            ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                          (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0110 (D : Class) (R : Class) :
    (nb096AlphaDummy003 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb096AlphaDummy003, fv_syn_cpw1] using (nb096_focused_notmem_0003 D R)

theorem nb096_focused_notmem_0004 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy004 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv q) (synCpw1 (synCpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb096_wpp_notmem_0111 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy004 D R q) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb096AlphaDummy004, fv_syn_cpw1] using (nb096_focused_notmem_0004 D R q)

theorem nb096_compact_envfresh_0007 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TEnvFresh
      [((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      ((synCpw1 (synCpw1 D))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096AlphaDummy001 D R) (nb096AlphaDummy002 D R q)
      (nb096_wpp_notmem_0106 D R) (nb096_wpp_notmem_0107 D R q)
      (TEnvFresh.consFresh (nb096AlphaDummy000 D R) q (nb096_wpp_notmem_0108 D R)
        (nb096_wpp_notmem_0109 D q dv_D_q)
        (TEnvFresh.consFresh (nb096AlphaDummy003 D R) (nb096AlphaDummy004 D R q)
          (nb096_wpp_notmem_0110 D R) (nb096_wpp_notmem_0111 D R q)
          (TEnvFresh.nil ((synCpw1 (synCpw1 D))).fv))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
