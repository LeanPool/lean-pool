/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C097M3Part001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4H5C097M3Part001`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb097_split_alpha_0000`. -/
@[expose]
noncomputable def nb097SplitAlpha0000 (C : Class) (k : Var) (m : Var) (F : Class) :
    TAlphaWff
      [((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      (Wff.imp (Wff.classMem (Class.cv (nb097AlphaDummy009 C F))
          (Class.cv (nb097AlphaDummy000 C F))) (Wff.neg
          (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
            (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb097AlphaDummy011 k m)) (Class.cv k)) (Wff.neg
          (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
            (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy009 C F) from
            (by
              unfold nb097AlphaDummy009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))))
          (show k ≠ (nb097AlphaDummy011 k m) from (by
              unfold nb097AlphaDummy011;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))))
          (TAlphaVar.there (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy008 C F) from
              (by
                unfold nb097AlphaDummy008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))))
            (show k ≠ (nb097AlphaDummy010 k m) from (by
                unfold nb097AlphaDummy010;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))))
            (TAlphaVar.there
              (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy038 C F) from (by
                  unfold nb097AlphaDummy038;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0032 C F) 0))))
              (show k ≠ (nb097AlphaDummy039 k m) from (by
                  unfold nb097AlphaDummy039;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0033 k m) 0))))
              (TAlphaVar.there
                (show (nb097AlphaDummy000 C F) ≠ (nb097AlphaDummy012 C F) from (by
                    unfold nb097AlphaDummy012;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0029 C F) 0))))
                (show k ≠ (nb097AlphaDummy013 k m) from (by
                    unfold nb097AlphaDummy013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0031 k m) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
                ((Class.cv (nb097AlphaDummy000 C F))).fv) (by decide))
            (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy016 C F)
                                      from (by
                                        unfold nb097AlphaDummy016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 0)))) (show
                                      (nb097AlphaDummy011 k m) ≠ (nb097AlphaDummy018 k m)
                                      from (by
                                        unfold nb097AlphaDummy018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 0))))
                                    (TAlphaVar.there (show (nb097AlphaDummy009 C F) ≠
        (nb097AlphaDummy017 C F) from (by
                                          unfold nb097AlphaDummy017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0006 C F) 1)))) (show
                                        (nb097AlphaDummy011 k m) ≠
        (nb097AlphaDummy019 k m) from (by
                                          unfold nb097AlphaDummy019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0007 k m) 1))))
                                      (TAlphaVar.there (show (nb097AlphaDummy009 C F) ≠
        (nb097AlphaDummy042 C F) from (by
          unfold nb097AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0036 C F) 0)))) (show (nb097AlphaDummy011 k m) ≠
        (nb097AlphaDummy043 k m) from (by
          unfold nb097AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0037 k m) 0)))) (TAlphaVar.there (show
        (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy040 C F) from (by
          unfold nb097AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0034 C F) 0)))) (show (nb097AlphaDummy011 k m) ≠
        (nb097AlphaDummy041 k m) from (by
          unfold nb097AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0035 k m) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb097AlphaDummy009 C F))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb097AlphaDummy011 k m))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy023 C F) from
        (by
          unfold nb097AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  1)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy026 k m) from (by
          unfold nb097AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  1)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy022 C F) from (by
          unfold nb097AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy025 k m) from (by
          unfold nb097AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold
            nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold
            nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023
        C F) ≠ (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠ (nb097AlphaDummy036 C F) from
        (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy036 C F) from (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from
        (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy016 C F)
                                      from (by
                                        unfold nb097AlphaDummy016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 0)))) (show
                                      (nb097AlphaDummy011 k m) ≠ (nb097AlphaDummy018 k m)
                                      from (by
                                        unfold nb097AlphaDummy018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 0))))
                                    (TAlphaVar.there (show (nb097AlphaDummy009 C F) ≠
        (nb097AlphaDummy017 C F) from (by
                                          unfold nb097AlphaDummy017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0006 C F) 1)))) (show
                                        (nb097AlphaDummy011 k m) ≠
        (nb097AlphaDummy019 k m) from (by
                                          unfold nb097AlphaDummy019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0007 k m) 1))))
                                      (TAlphaVar.there (show (nb097AlphaDummy009 C F) ≠
        (nb097AlphaDummy042 C F) from (by
          unfold nb097AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0036 C F) 0)))) (show (nb097AlphaDummy011 k m) ≠
        (nb097AlphaDummy043 k m) from (by
          unfold nb097AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0037 k m) 0)))) (TAlphaVar.there (show
        (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy040 C F) from (by
          unfold nb097AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0034 C F) 0)))) (show (nb097AlphaDummy011 k m) ≠
        (nb097AlphaDummy041 k m) from (by
          unfold nb097AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0035 k m) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb097AlphaDummy009 C F))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb097AlphaDummy011 k m))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy023 C F) from
        (by
          unfold nb097AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  1)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy026 k m) from (by
          unfold nb097AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  1)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy022 C F) from (by
          unfold nb097AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy025 k m) from (by
          unfold nb097AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold
            nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold
            nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023
        C F) ≠ (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠ (nb097AlphaDummy036 C F) from
        (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy036 C F) from (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from
        (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy042 C F), (nb097AlphaDummy043 k m)),
        ((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb097AlphaDummy040 C F), (nb097AlphaDummy041 k m)),
                    ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
                    ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
                    ((nb097AlphaDummy038 C F), (nb097AlphaDummy039 k m)),
                    ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
                    ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
                    ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
                    ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
                    ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4H5C097M3Part002`. -/


section

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

/-- Checked nominal proof certificate identified upstream as `nb097_split_alpha_0001`. -/
@[expose]
noncomputable def nb097SplitAlpha0001 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_k_m : k ≠ m) :
    TAlphaWff
      [((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      (Wff.imp (Wff.classMem (Class.cv (nb097AlphaDummy012 C F)) (synCcompl
            (Class.cab (nb097AlphaDummy008 C F)
              (synWrex (nb097AlphaDummy009 C F) (Class.cv (nb097AlphaDummy001 C F))
                (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                  (synCphi (Class.cv (nb097AlphaDummy009 C F)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb097AlphaDummy012 C F)) (synCcompl
              (Class.cab (nb097AlphaDummy008 C F) (synWrex (nb097AlphaDummy009 C F)
                  (Class.cv (nb097AlphaDummy000 C F))
                  (Wff.classEq (Class.cv (nb097AlphaDummy008 C F))
                    (synCun (synCphi (Class.cv (nb097AlphaDummy009 C F)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb097AlphaDummy013 k m)) (synCcompl
            (Class.cab (nb097AlphaDummy010 k m)
              (synWrex (nb097AlphaDummy011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                  (synCphi (Class.cv (nb097AlphaDummy011 k m)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb097AlphaDummy013 k m)) (synCcompl
              (Class.cab (nb097AlphaDummy010 k m)
                (synWrex (nb097AlphaDummy011 k m) (Class.cv k)
                  (Wff.classEq (Class.cv (nb097AlphaDummy010 k m))
                    (synCun (synCphi (Class.cv (nb097AlphaDummy011 k m)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy009 C F) from
                            (by
                              unfold nb097AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
                          (show m ≠ (nb097AlphaDummy011 k m) from (by
                              unfold nb097AlphaDummy011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
                          (TAlphaVar.there (show
                              (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy008 C F) from (by
                                unfold nb097AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
                            (show m ≠ (nb097AlphaDummy010 k m) from (by
                                unfold nb097AlphaDummy010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
                            (TAlphaVar.there (show
                                (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy014 C F) from
                                (by
                                  unfold nb097AlphaDummy014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0004 C F)
                                          0)))) (show m ≠ (nb097AlphaDummy015 k m) from (by
                                  unfold nb097AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0005 k m)
                                          0)))) (TAlphaVar.there (show
                                  (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy012 C F) from
                                  (by
                                    unfold nb097AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0001 C F)
                                            0)))) (show m ≠ (nb097AlphaDummy013 k m) from (by
                                    unfold nb097AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0003 k m)
                                            0)))) (TAlphaVar.there
                                  (freshVar_injective ((F).fv ∪ (C).fv) (by decide))
                                  (Ne.symm dv_k_m) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
                              ((Class.cv (nb097AlphaDummy000 C F))).fv) (by decide))
                          (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy016 C F)
                                    from (by
                                      unfold nb097AlphaDummy016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0006 C F)
                                              0)))) (show (nb097AlphaDummy011 k m) ≠
                                      (nb097AlphaDummy018 k m) from (by
                                      unfold nb097AlphaDummy018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0007 k m)
                                              0)))) (TAlphaVar.there (show
                                      (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy017 C F)
                                      from (by
                                        unfold nb097AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 1)))) (show
                                      (nb097AlphaDummy011 k m) ≠ (nb097AlphaDummy019 k m)
                                      from (by
                                        unfold nb097AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb097AlphaDummy009 C F))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb097AlphaDummy011 k m))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy023 C F) from (by
          unfold nb097AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010 C
                    F)
                  1)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy026 k m) from (by
          unfold nb097AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011 k
                    m)
                  1)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy022 C F) from (by
          unfold nb097AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy025 k m) from (by
          unfold nb097AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023
        C F) ≠ (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠ (nb097AlphaDummy036 C F) from
        (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy036 C F) from (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy009 C F) from
                            (by
                              unfold nb097AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
                          (show m ≠ (nb097AlphaDummy011 k m) from (by
                              unfold nb097AlphaDummy011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
                          (TAlphaVar.there (show
                              (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy008 C F) from (by
                                unfold nb097AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
                            (show m ≠ (nb097AlphaDummy010 k m) from (by
                                unfold nb097AlphaDummy010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
                            (TAlphaVar.there (show
                                (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy014 C F) from
                                (by
                                  unfold nb097AlphaDummy014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0004 C F)
                                          0)))) (show m ≠ (nb097AlphaDummy015 k m) from (by
                                  unfold nb097AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0005 k m)
                                          0)))) (TAlphaVar.there (show
                                  (nb097AlphaDummy001 C F) ≠ (nb097AlphaDummy012 C F) from
                                  (by
                                    unfold nb097AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0001 C F)
                                            0)))) (show m ≠ (nb097AlphaDummy013 k m) from (by
                                    unfold nb097AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0003 k m)
                                            0)))) (TAlphaVar.there
                                  (freshVar_injective ((F).fv ∪ (C).fv) (by decide))
                                  (Ne.symm dv_k_m) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb097AlphaDummy001 C F))).fv ∪
                              ((Class.cv (nb097AlphaDummy000 C F))).fv) (by decide))
                          (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy016 C F)
                                    from (by
                                      unfold nb097AlphaDummy016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0006 C F)
                                              0)))) (show (nb097AlphaDummy011 k m) ≠
                                      (nb097AlphaDummy018 k m) from (by
                                      unfold nb097AlphaDummy018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0007 k m)
                                              0)))) (TAlphaVar.there (show
                                      (nb097AlphaDummy009 C F) ≠ (nb097AlphaDummy017 C F)
                                      from (by
                                        unfold nb097AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 1)))) (show
                                      (nb097AlphaDummy011 k m) ≠ (nb097AlphaDummy019 k m)
                                      from (by
                                        unfold nb097AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb097AlphaDummy009 C F))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb097AlphaDummy011 k m))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy023 C F) from (by
          unfold nb097AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010 C
                    F)
                  1)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy026 k m) from (by
          unfold nb097AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011 k
                    m)
                  1)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy022 C F) from (by
          unfold nb097AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy025 k m) from (by
          unfold nb097AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097AlphaDummy018 k m) ≠ (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠ (nb097AlphaDummy030 C F) from
        (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy030 C F) from (by
          unfold
            nb097AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy031 k m) from (by
          unfold
            nb097AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy028 C F) from (by
          unfold
            nb097AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy029 k m) from (by
          unfold
            nb097AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy024 C F), (nb097AlphaDummy027 k m)),
        ((nb097AlphaDummy023 C F), (nb097AlphaDummy026 k m)),
        ((nb097AlphaDummy022 C F), (nb097AlphaDummy025 k m)),
        ((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097AlphaDummy016 C F))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097AlphaDummy018 k m))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy023
        C F) ≠ (nb097AlphaDummy034 C F) from (by
          unfold
            nb097AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy035 k m) from (by
          unfold
            nb097AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy023 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097AlphaDummy026 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097AlphaDummy016
        C F))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097AlphaDummy018 k m))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠ (nb097AlphaDummy036 C F) from
        (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097AlphaDummy024
        C F) ≠ (nb097AlphaDummy036 C F) from (by
          unfold
            nb097AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy037 k m) from (by
          unfold
            nb097AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097AlphaDummy024 C F) ≠
        (nb097AlphaDummy032 C F) from (by
          unfold
            nb097AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097AlphaDummy027 k m) ≠ (nb097AlphaDummy033 k m) from (by
          unfold
            nb097AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb097AlphaDummy016 C F) ≠
        (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb097AlphaDummy016 C F) ≠ (nb097AlphaDummy020 C F) from (by
          unfold nb097AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097AlphaDummy018 k m) ≠
        (nb097AlphaDummy021 k m) from (by
          unfold nb097AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed
        [((nb097AlphaDummy020 C F), (nb097AlphaDummy021 k m)),
        ((nb097AlphaDummy016 C F), (nb097AlphaDummy018 k m)),
        ((nb097AlphaDummy017 C F), (nb097AlphaDummy019 k m)),
        ((nb097AlphaDummy009 C F), (nb097AlphaDummy011 k m)),
        ((nb097AlphaDummy008 C F), (nb097AlphaDummy010 k m)),
        ((nb097AlphaDummy014 C F), (nb097AlphaDummy015 k m)),
        ((nb097AlphaDummy012 C F), (nb097AlphaDummy013 k m)),
        ((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb097SplitAlpha0000 C k m F)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb097SplitAlpha0000 C k m F)))))))))))

theorem nb097_wpp_notmem_0132 (C : Class) (F : Class) :
    (nb097AlphaDummy000 C F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy000, fv_syn_clec] using (nb097_compact_fv_empty_0020 C F)

theorem nb097_wpp_notmem_0133 (k : Var) : k ∉ ((synClec)).fv := by
  simpa only [fv_syn_clec] using (nb097_compact_fv_empty_0021 k)

theorem nb097_wpp_notmem_0134 (C : Class) (F : Class) :
    (nb097AlphaDummy001 C F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy001, fv_syn_clec] using (nb097_compact_fv_empty_0022 C F)

theorem nb097_wpp_notmem_0135 (m : Var) : m ∉ ((synClec)).fv := by
  simpa only [fv_syn_clec] using (nb097_compact_fv_empty_0023 m)

theorem nb097_wpp_notmem_0136 (C : Class) (F : Class) :
    (nb097AlphaDummy002 C F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy002, fv_syn_clec] using (nb097_compact_fv_empty_0024 C F)

theorem nb097_wpp_notmem_0137 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy003 C k m F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy003, fv_syn_clec] using
    (nb097_compact_fv_empty_0025 C k m F)

theorem nb097_wpp_notmem_0138 (C : Class) (F : Class) :
    (nb097AlphaDummy005 C F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy005, fv_syn_clec] using (nb097_compact_fv_empty_0026 C F)

theorem nb097_wpp_notmem_0139 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy007 C k m F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy007, fv_syn_clec] using
    (nb097_compact_fv_empty_0027 C k m F)

theorem nb097_wpp_notmem_0140 (C : Class) (F : Class) :
    (nb097AlphaDummy004 C F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy004, fv_syn_clec] using (nb097_compact_fv_empty_0028 C F)

theorem nb097_wpp_notmem_0141 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097AlphaDummy006 C k m F) ∉ ((synClec)).fv := by
  simpa only [nb097AlphaDummy006, fv_syn_clec] using
    (nb097_compact_fv_empty_0029 C k m F)

theorem nb097_compact_envfresh_0009 (C : Class) (k : Var) (m : Var) (F : Class) :
    TEnvFresh
      [((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      ((synClec)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb097AlphaDummy000 C F) k (nb097_wpp_notmem_0132 C F)
      (nb097_wpp_notmem_0133 k)
      (TEnvFresh.consFresh (nb097AlphaDummy001 C F) m (nb097_wpp_notmem_0134 C F)
        (nb097_wpp_notmem_0135 m)
        (TEnvFresh.consFresh (nb097AlphaDummy002 C F) (nb097AlphaDummy003 C k m F)
          (nb097_wpp_notmem_0136 C F) (nb097_wpp_notmem_0137 C k m F)
          (TEnvFresh.consFresh (nb097AlphaDummy005 C F) (nb097AlphaDummy007 C k m F)
            (nb097_wpp_notmem_0138 C F) (nb097_wpp_notmem_0139 C k m F)
            (TEnvFresh.consFresh (nb097AlphaDummy004 C F)
              (nb097AlphaDummy006 C k m F) (nb097_wpp_notmem_0140 C F)
              (nb097_wpp_notmem_0141 C k m F) (TEnvFresh.nil ((synClec)).fv))))))

/-- Checked nominal proof certificate identified upstream as `nb097_wpp_refl_0009`. -/
@[expose]
noncomputable def nb097WppRefl0009 (C : Class) (k : Var) (m : Var) (F : Class) :
    TReflOn
      [((nb097AlphaDummy000 C F), k), ((nb097AlphaDummy001 C F), m),
        ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
        ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
        ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
      ((synClec)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0009 C k m F)

/-- Checked nominal proof certificate identified upstream as `nominal_df_wppgamma`. -/
@[expose]
noncomputable def nominalDfWppgamma (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv)
    (dv_k_m : k ≠ m) :
    Nominal.NPrf
      (.classEq (synCwppgamma F C) (synCio m (synWa (.classMem (.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab (nb097AlphaDummy002 C F) (Wff.classEq
                        (Class.cab (nb097AlphaDummy001 C F) (synWa
                            (Wff.classMem (Class.cv (nb097AlphaDummy001 C F))
                              (synCwppcand F C))
                            (synWral (nb097AlphaDummy000 C F) (synCwppcand F C)
                              (synWbr (Class.cv (nb097AlphaDummy001 C F)) (synClec)
                                (Class.cv (nb097AlphaDummy000 C F))))))
                        (synCsn (Class.cv (nb097AlphaDummy002 C F)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb097AlphaDummy003 C k m F) (Wff.classEq
                        (Class.cab m (synWa (Wff.classMem (Class.cv m) (synCwppcand F C))
                            (synWral k (synCwppcand F C)
                              (synWbr (Class.cv m) (synClec) (Class.cv k)))))
                        (synCsn (Class.cv (nb097AlphaDummy003 C k m F)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb097AlphaDummy001 C F), m),
                            ((nb097AlphaDummy002 C F), (nb097AlphaDummy003 C k m F)),
                            ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
                            ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
                          (synCwppcand F C) (nb097WppRefl0000 C k m F dv_C_m dv_F_m)))
                      (TAlphaWff.all (TAlphaWff.imp
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.reflOfReflOn [((nb097AlphaDummy000 C F), k),
                                ((nb097AlphaDummy001 C F), m), ((nb097AlphaDummy002 C F),
                                  (nb097AlphaDummy003 C k m F)),
                                ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
                                ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
                              (synCwppcand F C)
                              (nb097WppRefl0001 C k m F dv_C_k dv_C_m dv_F_k dv_F_m)))
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb097SplitAlpha0001 C k m F dv_k_m))))
                            (TAlphaClass.reflOfReflOn [((nb097AlphaDummy000 C F), k),
                                ((nb097AlphaDummy001 C F), m), ((nb097AlphaDummy002 C F),
                                  (nb097AlphaDummy003 C k m F)),
                                ((nb097AlphaDummy005 C F), (nb097AlphaDummy007 C k m F)),
                                ((nb097AlphaDummy004 C F), (nb097AlphaDummy006 C k m F))]
                              (synClec) (nb097WppRefl0009 C k m F))))))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb097AlphaDummy002 C F) ≠ (nb097AlphaDummy044 C F) from
                            (by
                              unfold nb097AlphaDummy044;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0038 C F) 0)))) (show
                            (nb097AlphaDummy003 C k m F) ≠ (nb097AlphaDummy045 C k m F)
                            from (by
                              unfold nb097AlphaDummy045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0039 C k m F)
                                      0)))) (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
