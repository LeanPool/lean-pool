/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block006

/-! NF weak partition development: NAR4C090C001Part024. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0000`. -/
@[expose]
noncomputable def nb090SplitAlpha0000 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy035 A), (nb090AlphaDummy036 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy035 A))
          (Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy035 A))
            (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy036 v u))
          (Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy036 v u))
            (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy006 A) from (by
                      unfold nb090AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
                  (show v ≠ (nb090AlphaDummy008 v u) from (by
                      unfold nb090AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0034 v u) 1)))) (TAlphaVar.there
                    (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy005 A) from (by
                        unfold nb090AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
                    (show v ≠ (nb090AlphaDummy007 v u) from (by
                        unfold nb090AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy035 A) from (by
                          unfold nb090AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0036 A) 0))))
                      (show v ≠ (nb090AlphaDummy036 v u) from (by
                          unfold nb090AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0037 v u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy009 A) from (by
                            unfold nb090AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0033 A) 0))))
                        (show v ≠ (nb090AlphaDummy010 v u) from (by
                            unfold nb090AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0035 v u) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy002 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy013 A) from (by
          unfold nb090AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy015 v u) from (by
          unfold nb090AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy014 A) from (by
          unfold nb090AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy016 v u) from (by
          unfold nb090AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy039 A) from (by
          unfold nb090AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy040 v u) from (by
          unfold nb090AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy037 A) from (by
          unfold nb090AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090AlphaDummy008 v u) ≠ (nb090AlphaDummy038 v u) from (by
          unfold nb090AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy006 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy008 v u))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy020 A) from (by
          unfold
            nb090AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy023 v u) from (by
          unfold
            nb090AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy019 A) from (by
          unfold
            nb090AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy022 v u) from (by
          unfold
            nb090AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold
            nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold
            nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020
        A) ≠ (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy013 A) from (by
          unfold nb090AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy015 v u) from (by
          unfold nb090AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy014 A) from (by
          unfold nb090AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy016 v u) from (by
          unfold nb090AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy039 A) from (by
          unfold nb090AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy040 v u) from (by
          unfold nb090AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy037 A) from (by
          unfold nb090AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090AlphaDummy008 v u) ≠ (nb090AlphaDummy038 v u) from (by
          unfold nb090AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy006 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy008 v u))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy020 A) from (by
          unfold
            nb090AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy023 v u) from (by
          unfold
            nb090AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy019 A) from (by
          unfold
            nb090AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy022 v u) from (by
          unfold
            nb090AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold
            nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold
            nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020
        A) ≠ (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb090AlphaDummy037 A), (nb090AlphaDummy038 v u)),
                          ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
                          ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)),
                          ((nb090AlphaDummy035 A), (nb090AlphaDummy036 v u)),
                          ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
                          ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
                          ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy006 A) from (by
                        unfold nb090AlphaDummy006;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
                    (show v ≠ (nb090AlphaDummy008 v u) from (by
                        unfold nb090AlphaDummy008;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy005 A) from (by
                          unfold nb090AlphaDummy005;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
                      (show v ≠ (nb090AlphaDummy007 v u) from (by
                          unfold nb090AlphaDummy007;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy035 A) from (by
                            unfold nb090AlphaDummy035;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0036 A) 0))))
                        (show v ≠ (nb090AlphaDummy036 v u) from (by
                            unfold nb090AlphaDummy036;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0037 v u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy009 A) from (by
                              unfold nb090AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0033 A) 0))))
                          (show v ≠ (nb090AlphaDummy010 v u) from (by
                              unfold nb090AlphaDummy010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0035 v u) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy002 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy013 A) from (by
          unfold nb090AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy015 v u) from (by
          unfold nb090AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy014 A) from (by
          unfold nb090AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy016 v u) from (by
          unfold nb090AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy039 A) from (by
          unfold nb090AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A)
                  0)))) (show (nb090AlphaDummy008 v u) ≠ (nb090AlphaDummy040 v u) from (by
          unfold nb090AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy037 A) from (by
          unfold nb090AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090AlphaDummy008 v u) ≠ (nb090AlphaDummy038 v u) from (by
          unfold nb090AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy006 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy008 v u))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013
        A) ≠ (nb090AlphaDummy020 A) from (by
          unfold
            nb090AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy023 v u) from (by
          unfold
            nb090AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy019 A) from (by
          unfold
            nb090AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy022 v u) from (by
          unfold
            nb090AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold
            nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold
            nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020
        A) ≠ (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy013 A) from (by
          unfold nb090AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy015 v u) from (by
          unfold nb090AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy014 A) from (by
          unfold nb090AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy016 v u) from (by
          unfold nb090AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy039 A) from (by
          unfold nb090AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0040 A)
                  0)))) (show (nb090AlphaDummy008 v u) ≠ (nb090AlphaDummy040 v u) from (by
          unfold nb090AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0041 v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy037 A) from (by
          unfold nb090AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0038 A)
                  0)))) (show (nb090AlphaDummy008 v u) ≠ (nb090AlphaDummy038 v u) from (by
          unfold nb090AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0039 v u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy006 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy008 v u))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013
        A) ≠ (nb090AlphaDummy020 A) from (by
          unfold
            nb090AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy023 v u) from (by
          unfold
            nb090AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy019 A) from (by
          unfold
            nb090AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy022 v u) from (by
          unfold
            nb090AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold
            nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold
            nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003
        A), (nb090AlphaDummy004 v u A h))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020
        A) ≠ (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy039 A), (nb090AlphaDummy040 v u)), ((nb090AlphaDummy037 A),
        (nb090AlphaDummy038 v u)), ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
        ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)), ((nb090AlphaDummy035 A),
        (nb090AlphaDummy036 v u)), ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy037 A), (nb090AlphaDummy038 v u)),
                            ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)),
                            ((nb090AlphaDummy005 A), (nb090AlphaDummy007 v u)),
                            ((nb090AlphaDummy035 A), (nb090AlphaDummy036 v u)),
                            ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
                            ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb090_focused_notmem_0000 (A : Class) : (nb090AlphaDummy002 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 2 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => hu)

theorem nb090_wpp_notmem_0106 (A : Class) :
    (nb090AlphaDummy002 A) ∉ ((synChwcodes A)).fv := by
  simpa only [nb090AlphaDummy002, fv_syn_chwcodes] using (nb090_focused_notmem_0000 A)

theorem nb090_wpp_notmem_0107 (v : Var) (A : Class) (dv_A_v : v ∉ A.fv) :
    v ∉ ((synChwcodes A)).fv := by simpa only [fv_syn_chwcodes] using dv_A_v

theorem nb090_focused_notmem_0001 (A : Class) : (nb090AlphaDummy001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => hu)

theorem nb090_wpp_notmem_0108 (A : Class) :
    (nb090AlphaDummy001 A) ∉ ((synChwcodes A)).fv := by
  simpa only [nb090AlphaDummy001, fv_syn_chwcodes] using (nb090_focused_notmem_0001 A)

theorem nb090_wpp_notmem_0109 (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    u ∉ ((synChwcodes A)).fv := by simpa only [fv_syn_chwcodes] using dv_A_u

theorem nb090_focused_notmem_0002 (A : Class) : (nb090AlphaDummy003 A) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb090AlphaDummy001 A)} : Finset Var) ∪
            ({(nb090AlphaDummy002 A)} : Finset Var) ∪ ((synWa
              (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
                (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
              (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
                  (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                  (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                  (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
                  (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
        (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
      (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
          (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
          (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
      (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_chwcodes A]
  exact hu

theorem nb090_wpp_notmem_0110 (A : Class) :
    (nb090AlphaDummy003 A) ∉ ((synChwcodes A)).fv := by
  simpa only [nb090AlphaDummy003, fv_syn_chwcodes] using (nb090_focused_notmem_0002 A)

theorem nb090_focused_notmem_0003 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090AlphaDummy004 v u A h) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((synWa
              (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
                (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
                (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
                  (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
                  (synCfv (synC2nd) (Class.cv v)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
        (Wff.classMem (Class.cv v) (synChwcodes A)))
      (synWex h (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
          (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
          (synCfv (synC2nd) (Class.cv v))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (synChwcodes A))
      (Wff.classMem (Class.cv v) (synChwcodes A))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv u) (synChwcodes A)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_chwcodes A]
  exact hu

theorem nb090_wpp_notmem_0111 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090AlphaDummy004 v u A h) ∉ ((synChwcodes A)).fv := by
  simpa only [nb090AlphaDummy004, fv_syn_chwcodes] using
    (nb090_focused_notmem_0003 v u A h)

theorem nb090_compact_envfresh_0007 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    TEnvFresh
      [((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synChwcodes A)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy002 A) v (nb090_wpp_notmem_0106 A)
      (nb090_wpp_notmem_0107 v A dv_A_v)
      (TEnvFresh.consFresh (nb090AlphaDummy001 A) u (nb090_wpp_notmem_0108 A)
        (nb090_wpp_notmem_0109 u A dv_A_u)
        (TEnvFresh.consFresh (nb090AlphaDummy003 A) (nb090AlphaDummy004 v u A h)
          (nb090_wpp_notmem_0110 A) (nb090_wpp_notmem_0111 v u A h)
          (TEnvFresh.nil ((synChwcodes A)).fv))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0007`. -/
@[expose]
noncomputable def nb090WppRefl0007 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) :
    TReflOn
      [((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synChwcodes A)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0007 v u A h dv_A_u dv_A_v)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
