/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart002

/-! NF weak partition development: NAR4H5C091M3BPart003. -/


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

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0000`. -/
@[expose]
noncomputable def nb091SplitAlpha0000 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.neg (Wff.classMem (Class.cv (nb091AlphaDummy035 D R))
          (Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb091AlphaDummy036 D R p))
          (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
              (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy006 D R) from (by
                      unfold nb091AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
                  (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy008 D R p) from (by
                      unfold nb091AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
                  (TAlphaVar.there
                    (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy005 D R) from (by
                        unfold nb091AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
                    (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy007 D R p) from (by
                        unfold nb091AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy035 D R) from (by
                          unfold nb091AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0038 D R) 0))))
                      (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy036 D R p) from
                        (by
                          unfold nb091AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0039 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy009 D R) from (by
                            unfold nb091AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0035 D R) 0)))) (show
                          (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy010 D R p) from (by
                            unfold nb091AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0037 D R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
                      ((Class.cv (nb091AlphaDummy001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy013 D R) from (by
          unfold nb091AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy015 D R p) from (by
          unfold nb091AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy006 D R) ≠ (nb091AlphaDummy014 D R) from (by
          unfold nb091AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy016 D R p) from (by
          unfold nb091AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy039 D R) from (by
          unfold nb091AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy040 D R p) from
        (by
          unfold nb091AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy037 D R) from (by
          unfold nb091AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy038 D R p) from
        (by
          unfold nb091AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D
        R) ≠ (nb091AlphaDummy020 D R) from (by
          unfold
            nb091AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy023 D R p) from
        (by
          unfold
            nb091AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy019 D R) from (by
          unfold
            nb091AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy022 D R p) from
        (by
          unfold
            nb091AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold
            nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold
            nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D
        R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039 D
        R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D
        R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009 D
        R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from
        (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020
        D R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018
        D R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039
        D R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008
        D R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009
        D R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠ (nb091AlphaDummy033 D R) from
        (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy033 D R) from (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy013 D R) from (by
          unfold nb091AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy015 D R p) from (by
          unfold nb091AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy006 D R) ≠ (nb091AlphaDummy014 D R) from (by
          unfold nb091AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy016 D R p) from (by
          unfold nb091AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy039 D R) from (by
          unfold nb091AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy040 D R p) from
        (by
          unfold nb091AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy037 D R) from (by
          unfold nb091AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy038 D R p) from
        (by
          unfold nb091AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D
        R) ≠ (nb091AlphaDummy020 D R) from (by
          unfold
            nb091AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy023 D R p) from
        (by
          unfold
            nb091AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy019 D R) from (by
          unfold
            nb091AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy022 D R p) from
        (by
          unfold
            nb091AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold
            nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold
            nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D
        R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039 D
        R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D
        R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009 D
        R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from
        (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020
        D R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018
        D R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039
        D R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008
        D R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009
        D R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠ (nb091AlphaDummy033 D R) from
        (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy033 D R) from (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
                          ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
                          ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
                          ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
                          ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
                          ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                          ((nb091AlphaDummy000 D R), p),
                          ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0001`. -/
@[expose]
noncomputable def nb091SplitAlpha0001 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy035 D R))
          (Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy035 D R))
            (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy036 D R p))
          (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
              (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy036 D R p))
            (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
                (Class.cv (nb091AlphaDummy002 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy006 D R) from (by
                      unfold nb091AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
                  (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy008 D R p) from (by
                      unfold nb091AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
                  (TAlphaVar.there
                    (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy005 D R) from (by
                        unfold nb091AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
                    (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy007 D R p) from (by
                        unfold nb091AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy035 D R) from (by
                          unfold nb091AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0038 D R) 0))))
                      (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy036 D R p) from
                        (by
                          unfold nb091AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0039 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy009 D R) from (by
                            unfold nb091AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0035 D R) 0)))) (show
                          (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy010 D R p) from (by
                            unfold nb091AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0037 D R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
                      ((Class.cv (nb091AlphaDummy001 D R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy013 D R) from (by
          unfold nb091AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy015 D R p) from (by
          unfold nb091AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy006 D R) ≠ (nb091AlphaDummy014 D R) from (by
          unfold nb091AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy016 D R p) from (by
          unfold nb091AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy039 D R) from (by
          unfold nb091AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy040 D R p) from
        (by
          unfold nb091AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy037 D R) from (by
          unfold nb091AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy038 D R p) from
        (by
          unfold nb091AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D
        R) ≠ (nb091AlphaDummy020 D R) from (by
          unfold
            nb091AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy023 D R p) from
        (by
          unfold
            nb091AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy019 D R) from (by
          unfold
            nb091AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy022 D R p) from
        (by
          unfold
            nb091AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold
            nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold
            nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D
        R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039 D
        R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D
        R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009 D
        R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from
        (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020
        D R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018
        D R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039
        D R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008
        D R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009
        D R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠ (nb091AlphaDummy033 D R) from
        (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy033 D R) from (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy013 D R) from (by
          unfold nb091AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy015 D R p) from (by
          unfold nb091AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy006 D R) ≠ (nb091AlphaDummy014 D R) from (by
          unfold nb091AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy016 D R p) from (by
          unfold nb091AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy039 D R) from (by
          unfold nb091AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0042 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy040 D R p) from
        (by
          unfold nb091AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0043 D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy037 D R) from (by
          unfold nb091AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0040 D R)
                  0)))) (show (nb091AlphaDummy008 D R p) ≠ (nb091AlphaDummy038 D R p) from
        (by
          unfold nb091AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0041 D R p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D
        R) ≠ (nb091AlphaDummy020 D R) from (by
          unfold
            nb091AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy023 D R p) from
        (by
          unfold
            nb091AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy019 D R) from (by
          unfold
            nb091AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy022 D R p) from
        (by
          unfold
            nb091AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold
            nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold
            nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D
        R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039 D
        R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D
        R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009 D
        R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from
        (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020
        D R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018
        D R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy039
        D R), (nb091AlphaDummy040 D R p)), ((nb091AlphaDummy037 D R),
        (nb091AlphaDummy038 D R p)), ((nb091AlphaDummy006 D R), (nb091AlphaDummy008
        D R p)), ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)), ((nb091AlphaDummy009
        D R), (nb091AlphaDummy010 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠ (nb091AlphaDummy033 D R) from
        (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy033 D R) from (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D
                    R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy039 D R), (nb091AlphaDummy040 D R p)),
        ((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb091AlphaDummy037 D R), (nb091AlphaDummy038 D R p)),
                          ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
                          ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
                          ((nb091AlphaDummy035 D R), (nb091AlphaDummy036 D R p)),
                          ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
                          ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                          ((nb091AlphaDummy000 D R), p),
                          ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb091SplitAlpha0000 D R p))

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0002`. -/
@[expose]
noncomputable def nb091SplitAlpha0002 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.classEq (Class.cv (nb091AlphaDummy003 D R))
        (synCop (Class.cv (nb091AlphaDummy000 D R)) (Class.cv (nb091AlphaDummy001 D R))))
      (Wff.classEq (Class.cv (nb091AlphaDummy004 D R p))
        (synCop (Class.cv p) (Class.cv (nb091AlphaDummy002 D R p)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy003 D R) from (by
              unfold nb091AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0002 D R) 0)))))
        (Ne.symm (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy004 D R p) from (by
              unfold nb091AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0003 D R p) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy003 D R) from (by
                unfold nb091AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0000 D R) 0)))))
          (Ne.symm (show p ≠ (nb091AlphaDummy004 D R p) from (by
                unfold nb091AlphaDummy004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0001 D R p) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
                                    (nb091AlphaDummy006 D R) from (by
                                    unfold nb091AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                            1)))) (show p ≠ (nb091AlphaDummy008 D R p) from
                                  (by
                                    unfold nb091AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0008 D R p)
                                            1)))) (TAlphaVar.there (show
                                    (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy005 D R)
                                    from (by
                                      unfold nb091AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                              0)))) (show p ≠ (nb091AlphaDummy007 D R p) from
                                    (by
                                      unfold nb091AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0008 D R p) 0))))
                                  (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
                                        (nb091AlphaDummy011 D R) from (by
                                        unfold nb091AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0010 D R) 0))))
                                    (show p ≠ (nb091AlphaDummy012 D R p) from (by
                                        unfold nb091AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0011 D R p) 0))))
                                    (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy009 D R) from (by
                                          unfold nb091AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0007 D R) 0))))
                                      (show p ≠ (nb091AlphaDummy010 D R p) from (by
                                          unfold nb091AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0009 D R p) 0))))
                                      (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy001 D R) from (by
          unfold nb091AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004 D R) 0))))
                                        (show p ≠ (nb091AlphaDummy002 D R p) from (by
          unfold nb091AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005 D R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
                                    ((Class.cv (nb091AlphaDummy001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb091AlphaDummy002 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy013 D R) from (by
          unfold nb091AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy015 D R p) from (by
          unfold nb091AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy006 D R) ≠ (nb091AlphaDummy014 D R) from (by
          unfold nb091AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy016 D R p) from (by
          unfold nb091AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb091AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy013 D R) ≠ (nb091AlphaDummy020 D R) from (by
          unfold
            nb091AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy023 D R p) from
        (by
          unfold
            nb091AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy019 D R) from (by
          unfold
            nb091AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy022 D R p) from
        (by
          unfold
            nb091AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold
            nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold
            nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R
        p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy006 D
        R), (nb091AlphaDummy008 D R p)), ((nb091AlphaDummy005 D R),
        (nb091AlphaDummy007 D R p)), ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D R
        p)), ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D
        R), p), ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from
        (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D
        R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy006 D
        R), (nb091AlphaDummy008 D R p)), ((nb091AlphaDummy005 D R),
        (nb091AlphaDummy007 D R p)), ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D
        R p)), ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D
        R), p), ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠ (nb091AlphaDummy033 D R) from
        (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy033 D R) from (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy013 D R) ≠ (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
                                    (nb091AlphaDummy006 D R) from (by
                                    unfold nb091AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                            1)))) (show p ≠ (nb091AlphaDummy008 D R p) from
                                  (by
                                    unfold nb091AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0008 D R p)
                                            1)))) (TAlphaVar.there (show
                                    (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy005 D R)
                                    from (by
                                      unfold nb091AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0006 D R)
                                              0)))) (show p ≠ (nb091AlphaDummy007 D R p) from
                                    (by
                                      unfold nb091AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0008 D R p) 0))))
                                  (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
                                        (nb091AlphaDummy011 D R) from (by
                                        unfold nb091AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0010 D R) 0))))
                                    (show p ≠ (nb091AlphaDummy012 D R p) from (by
                                        unfold nb091AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0011 D R p) 0))))
                                    (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy009 D R) from (by
                                          unfold nb091AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0007 D R) 0))))
                                      (show p ≠ (nb091AlphaDummy010 D R p) from (by
                                          unfold nb091AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0009 D R p) 0))))
                                      (TAlphaVar.there (show (nb091AlphaDummy000 D R) ≠
        (nb091AlphaDummy001 D R) from (by
          unfold nb091AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004 D R) 0))))
                                        (show p ≠ (nb091AlphaDummy002 D R p) from (by
          unfold nb091AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005 D R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
                                    ((Class.cv (nb091AlphaDummy001 D R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb091AlphaDummy002 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091AlphaDummy006 D R) ≠
        (nb091AlphaDummy013 D R) from (by
          unfold nb091AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 0)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy015 D R p) from (by
          unfold nb091AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy006 D R) ≠ (nb091AlphaDummy014 D R) from (by
          unfold nb091AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0012 D R) 1)))) (show (nb091AlphaDummy008 D R p) ≠
        (nb091AlphaDummy016 D R p) from (by
          unfold nb091AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0013 D R p) 1)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb091AlphaDummy006 D R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy008 D R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy013 D R) ≠ (nb091AlphaDummy020 D R) from (by
          unfold
            nb091AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  1)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy023 D R p) from
        (by
          unfold
            nb091AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy019 D R) from (by
          unfold
            nb091AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0016
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy022 D R p) from
        (by
          unfold
            nb091AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0017
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold
            nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014
                    D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold
            nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R
        p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy006 D
        R), (nb091AlphaDummy008 D R p)), ((nb091AlphaDummy005 D R),
        (nb091AlphaDummy007 D R p)), ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D R
        p)), ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D
        R), p), ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠ (nb091AlphaDummy027 D R) from
        (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0020
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0021
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0018
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0019
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy027 D R) from (by
          unfold
            nb091AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0024
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy028 D R p) from
        (by
          unfold
            nb091AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0025
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy025 D R) from (by
          unfold
            nb091AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0022
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy026 D R p) from
        (by
          unfold
            nb091AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0023
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy021 D R), (nb091AlphaDummy024 D R p)), ((nb091AlphaDummy020 D
        R), (nb091AlphaDummy023 D R p)), ((nb091AlphaDummy019 D R),
        (nb091AlphaDummy022 D R p)), ((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D
        R p)), ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)), ((nb091AlphaDummy006 D
        R), (nb091AlphaDummy008 D R p)), ((nb091AlphaDummy005 D R),
        (nb091AlphaDummy007 D R p)), ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D
        R p)), ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D
        R), p), ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy020 D
        R) ≠ (nb091AlphaDummy031 D R) from (by
          unfold
            nb091AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0028
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy032 D R p) from
        (by
          unfold
            nb091AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0029
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy020 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0026
                    D
                    R)
                  0)))) (show (nb091AlphaDummy023 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0027
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy013
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠ (nb091AlphaDummy033 D R) from
        (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy021 D
        R) ≠ (nb091AlphaDummy033 D R) from (by
          unfold
            nb091AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0032
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy034 D R p) from
        (by
          unfold
            nb091AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0033
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy021 D R) ≠
        (nb091AlphaDummy029 D R) from (by
          unfold
            nb091AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0030
                    D
                    R)
                  0)))) (show (nb091AlphaDummy024 D R p) ≠ (nb091AlphaDummy030 D R p) from
        (by
          unfold
            nb091AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0031
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy013 D R) ≠ (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy013 D R) ≠
        (nb091AlphaDummy017 D R) from (by
          unfold nb091AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0014 D R)
                  0)))) (show (nb091AlphaDummy015 D R p) ≠ (nb091AlphaDummy018 D R p) from
        (by
          unfold nb091AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0015 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy017 D R), (nb091AlphaDummy018 D R p)),
        ((nb091AlphaDummy013 D R), (nb091AlphaDummy015 D R p)),
        ((nb091AlphaDummy014 D R), (nb091AlphaDummy016 D R p)),
        ((nb091AlphaDummy006 D R), (nb091AlphaDummy008 D R p)),
        ((nb091AlphaDummy005 D R), (nb091AlphaDummy007 D R p)),
        ((nb091AlphaDummy011 D R), (nb091AlphaDummy012 D R p)),
        ((nb091AlphaDummy009 D R), (nb091AlphaDummy010 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb091SplitAlpha0001 D R p)))))))))

theorem nb091_focused_notmem_0000 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCec
              (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
              (synChwniso D))).fv)
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

theorem nb091_wpp_notmem_0106 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb091AlphaDummy001, fv_syn_cpw1] using (nb091_focused_notmem_0000 D R)

theorem nb091_focused_notmem_0001 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
          ((synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
              (synChwniso D))).fv)
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

theorem nb091_wpp_notmem_0107 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb091AlphaDummy002, fv_syn_cpw1] using (nb091_focused_notmem_0001 D R p)

theorem nb091_focused_notmem_0002 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb091_wpp_notmem_0108 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb091AlphaDummy000, fv_syn_cpw1] using (nb091_focused_notmem_0002 D R)

theorem nb091_wpp_notmem_0109 (D : Class) (p : Var) (dv_D_p : p ∉ D.fv) :
    p ∉ ((synCpw1 (synCpw1 D))).fv := by simpa only [fv_syn_cpw1] using dv_D_p

theorem nb091_focused_notmem_0003 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
            ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
                  (synChwniso D))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))) (synChwniso D)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb091_wpp_notmem_0110 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb091AlphaDummy003, fv_syn_cpw1] using (nb091_focused_notmem_0003 D R)

theorem nb091_focused_notmem_0004 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
                (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
                  (synChwniso D))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
        (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv p) (synCpw1 (synCpw1 D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 D)]
  rw [fv_syn_cpw1 D]
  exact hu

theorem nb091_wpp_notmem_0111 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb091AlphaDummy004, fv_syn_cpw1] using (nb091_focused_notmem_0004 D R p)

theorem nb091_compact_envfresh_0007 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TEnvFresh
      [((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      ((synCpw1 (synCpw1 D))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091AlphaDummy001 D R) (nb091AlphaDummy002 D R p)
      (nb091_wpp_notmem_0106 D R) (nb091_wpp_notmem_0107 D R p)
      (TEnvFresh.consFresh (nb091AlphaDummy000 D R) p (nb091_wpp_notmem_0108 D R)
        (nb091_wpp_notmem_0109 D p dv_D_p)
        (TEnvFresh.consFresh (nb091AlphaDummy003 D R) (nb091AlphaDummy004 D R p)
          (nb091_wpp_notmem_0110 D R) (nb091_wpp_notmem_0111 D R p)
          (TEnvFresh.nil ((synCpw1 (synCpw1 D))).fv))))

/-- Checked nominal proof certificate identified upstream as `nb091_wpp_refl_0007`. -/
@[expose]
noncomputable def nb091WppRefl0007 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TReflOn
      [((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      ((synCpw1 (synCpw1 D))).fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0007 D R p dv_D_p)

theorem nb091_focused_notmem_0005 (D : Class) (R : Class) :
    (nb091AlphaDummy057 D R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0006 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy058 D R p) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb091_focused_notmem_0007 (D : Class) (R : Class) :
    (nb091AlphaDummy055 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
          ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0008 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy056 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCnin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0009 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0010 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0011 (D : Class) (R : Class) :
    (nb091AlphaDummy047 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0012 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy049 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0013 (D : Class) (R : Class) :
    (nb091AlphaDummy053 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv ∪
          ((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091AlphaDummy047 D R)
      (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0011 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy048 D R)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0009 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0014 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy054 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv ∪
          ((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091AlphaDummy049 D R p)
      (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0012 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy050 D R p)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0010 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0015 (D : Class) (R : Class) :
    (nb091AlphaDummy051 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb091AlphaDummy047 D R)
                (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                              (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                              (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                    (synCphi (Class.cv (nb091AlphaDummy048 D R)))))))).fv ∪ ((synCcompl
              (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                    (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
          (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
            (synCphi (Class.cv (nb091AlphaDummy048 D R))))))]
  rw [fv_class_cab (nb091AlphaDummy047 D R)
      (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0011 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy048 D R)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0009 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0016 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy052 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb091AlphaDummy049 D R p)
                (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (synCuni (synCuni (Class.cv p))))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                    (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))))).fv ∪ ((synCcompl
              (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                    (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
          (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))
          (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
            (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))]
  rw [fv_class_cab (nb091AlphaDummy049 D R p)
      (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0012 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy050 D R p)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0010 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0017 (D : Class) (R : Class) :
    (nb091AlphaDummy045 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0018 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy046 D R p) ∉ R.fv :=
  by
  change freshVar (((synChnwcutcode R D (synCuni (synCuni (Class.cv p))))).fv) 0 ∉ R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0019 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))]
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0020 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪
          ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))]
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0021 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))]
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0022 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪
          ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))]
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0023 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCec
              (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
              (synChwniso D))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec
      (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
      (synChwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0024 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
          ((synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
              (synChwniso D))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0025 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0026 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
            ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
                  (synChwniso D))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))) (synChwniso D)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb091AlphaDummy001 D R))
      (synCec
        (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
        (synChwniso D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec
      (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
      (synChwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0027 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
                (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
                  (synChwniso D))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
        (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb091AlphaDummy002 D R p))
      (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv p)))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_compact_envfresh_0008 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TEnvFresh
      [((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091AlphaDummy057 D R) (nb091AlphaDummy058 D R p)
      (nb091_focused_notmem_0005 D R) (nb091_focused_notmem_0006 D R p)
      (TEnvFresh.consFresh (nb091AlphaDummy055 D R) (nb091AlphaDummy056 D R p)
        (nb091_focused_notmem_0007 D R) (nb091_focused_notmem_0008 D R p)
        (TEnvFresh.consFresh (nb091AlphaDummy048 D R) (nb091AlphaDummy050 D R p)
          (nb091_focused_notmem_0009 D R) (nb091_focused_notmem_0010 D R p)
          (TEnvFresh.consFresh (nb091AlphaDummy047 D R) (nb091AlphaDummy049 D R p)
            (nb091_focused_notmem_0011 D R) (nb091_focused_notmem_0012 D R p)
            (TEnvFresh.consFresh (nb091AlphaDummy053 D R) (nb091AlphaDummy054 D R p)
              (nb091_focused_notmem_0013 D R) (nb091_focused_notmem_0014 D R p)
              (TEnvFresh.consFresh (nb091AlphaDummy051 D R)
                (nb091AlphaDummy052 D R p) (nb091_focused_notmem_0015 D R)
                (nb091_focused_notmem_0016 D R p)
                (TEnvFresh.consFresh (nb091AlphaDummy045 D R)
                  (nb091AlphaDummy046 D R p) (nb091_focused_notmem_0017 D R)
                  (nb091_focused_notmem_0018 D R p)
                  (TEnvFresh.consFresh (nb091AlphaDummy042 D R)
                    (nb091AlphaDummy044 D R p) (nb091_focused_notmem_0019 D R)
                    (nb091_focused_notmem_0020 D R p)
                    (TEnvFresh.consFresh (nb091AlphaDummy041 D R)
                      (nb091AlphaDummy043 D R p) (nb091_focused_notmem_0021 D R)
                      (nb091_focused_notmem_0022 D R p)
                      (TEnvFresh.consFresh (nb091AlphaDummy001 D R)
                        (nb091AlphaDummy002 D R p) (nb091_focused_notmem_0023 D R)
                        (nb091_focused_notmem_0024 D R p)
                        (TEnvFresh.consFresh (nb091AlphaDummy000 D R) p
                          (nb091_focused_notmem_0025 D R) dv_R_p
                          (TEnvFresh.consFresh (nb091AlphaDummy003 D R)
                            (nb091AlphaDummy004 D R p) (nb091_focused_notmem_0026 D R)
                            (nb091_focused_notmem_0027 D R p) (TEnvFresh.nil R.fv)))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb091_focused_refl_0000`. -/
@[expose]
noncomputable def nb091FocusedRefl0000 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TReflOn
      [((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      R.fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0008 D R p dv_R_p)

theorem nb091_compact_fv_empty_0052 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0053 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0054 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0055 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0056 (D : Class) (R : Class) :
    (nb091AlphaDummy063 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0057 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy064 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0058 (D : Class) (R : Class) :
    (nb091AlphaDummy057 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0059 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy058 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0060 (D : Class) (R : Class) :
    (nb091AlphaDummy055 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0061 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy056 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0062 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0063 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0064 (D : Class) (R : Class) :
    (nb091AlphaDummy047 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0065 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy049 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0066 (D : Class) (R : Class) :
    (nb091AlphaDummy053 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0067 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy054 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0068 (D : Class) (R : Class) :
    (nb091AlphaDummy051 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0069 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy052 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0070 (D : Class) (R : Class) :
    (nb091AlphaDummy045 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0071 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy046 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0072 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0073 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0074 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0075 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
