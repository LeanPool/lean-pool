/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C076C001Part005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C076C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0000`. -/
@[expose]
noncomputable def nb076SplitAlpha0000 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_m_n : m ≠ n) :
    TAlphaWff
      [((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
        ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
        ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)),
        ((nb076AlphaDummy009), (nb076AlphaDummy011 g m n a b)),
        ((nb076AlphaDummy015), (nb076AlphaDummy016 g m n a b)),
        ((nb076AlphaDummy013), (nb076AlphaDummy014 g m n a b)),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy023))
          (Class.cab (nb076AlphaDummy017)
            (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
              (Wff.classEq (Class.cv (nb076AlphaDummy017))
                (synCphi (Class.cv (nb076AlphaDummy018))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy023)) (Class.cab (nb076AlphaDummy017)
              (synWrex (nb076AlphaDummy018) (Class.cv (nb076AlphaDummy003))
                (Wff.classEq (Class.cv (nb076AlphaDummy017))
                  (synCphi (Class.cv (nb076AlphaDummy018)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy024 m n))
          (Class.cab (nb076AlphaDummy019 m n)
            (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                (synCphi (Class.cv (nb076AlphaDummy020 m n))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy024 m n))
            (Class.cab (nb076AlphaDummy019 m n)
              (synWrex (nb076AlphaDummy020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076AlphaDummy019 m n))
                  (synCphi (Class.cv (nb076AlphaDummy020 m n))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy018) from
                    (by
                      unfold nb076AlphaDummy018;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
                  (show m ≠ (nb076AlphaDummy020 m n) from (by
                      unfold nb076AlphaDummy020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0016 m n) 1)))) (TAlphaVar.there
                    (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy017) from (by
                        unfold nb076AlphaDummy017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))))
                    (show m ≠ (nb076AlphaDummy019 m n) from (by
                        unfold nb076AlphaDummy019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy023) from (by
                          unfold nb076AlphaDummy023;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0018) 0))))
                      (show m ≠ (nb076AlphaDummy024 m n) from (by
                          unfold nb076AlphaDummy024;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0019 m n) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy021) from (by
                            unfold nb076AlphaDummy021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0015) 0))))
                        (show m ≠ (nb076AlphaDummy022 m n) from (by
                            unfold nb076AlphaDummy022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0017 m n) 0))))
                        (TAlphaVar.there
                          (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy010) from (by
                              unfold nb076AlphaDummy010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0008) 1))))
                          (show m ≠ (nb076AlphaDummy012 g m n a b) from (by
                              unfold nb076AlphaDummy012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0010 g m n a b)
                                      1)))) (TAlphaVar.there
                            (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy009) from (by
                                unfold nb076AlphaDummy009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0008) 0))))
                            (show m ≠ (nb076AlphaDummy011 g m n a b) from (by
                                unfold nb076AlphaDummy011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0010 g m n a b)
                                        0)))) (TAlphaVar.there
                              (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy015) from (by
                                  unfold nb076AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0012) 0))))
                              (show m ≠ (nb076AlphaDummy016 g m n a b) from (by
                                  unfold nb076AlphaDummy016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb076_support_mem_0013 g m n a b) 0))))
                              (TAlphaVar.there
                                (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy013) from (by
                                    unfold nb076AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0009) 0))))
                                (show m ≠ (nb076AlphaDummy014 g m n a b) from (by
                                    unfold nb076AlphaDummy014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb076_support_mem_0011 g m n a b) 0))))
                                (TAlphaVar.there
                                  (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy005) from
                                    (by
                                      unfold nb076AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0006)
                                              0))))
                                  (show m ≠ (nb076AlphaDummy006 g m n a b) from (by
                                      unfold nb076AlphaDummy006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0007 g m n a b) 0))))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_m_n (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb076AlphaDummy003))).fv ∪
                      ((Class.cv (nb076AlphaDummy004))).fv) (by decide))
                  (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy025) from (by
                              unfold nb076AlphaDummy025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0020) 0))))
                          (show (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy027 m n) from
                            (by
                              unfold nb076AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy026) from (by
                                unfold nb076AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                              (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy028 m n) from (by
                                unfold nb076AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076AlphaDummy018))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076AlphaDummy020 m n))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy032) from (by
          unfold nb076AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy035 m n) from (by
          unfold nb076AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy025) ≠ (nb076AlphaDummy031) from (by
          unfold nb076AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy034 m n) from (by
          unfold nb076AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029)
        from (by
          unfold nb076AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy030 m n) from (by
          unfold nb076AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)), ((nb076AlphaDummy017),
        (nb076AlphaDummy019 m n)), ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
        ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠
        (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)), ((nb076AlphaDummy017),
        (nb076AlphaDummy019 m n)), ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
        ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy027 m
        n))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043) from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043)
        from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠
        (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                    ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                    ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                    ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                    ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                    ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
                                    ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from
                                    (by
                                      unfold nb076AlphaDummy029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0022)
                                              0)))) (show (nb076AlphaDummy027 m n) ≠
                                      (nb076AlphaDummy030 m n) from (by
                                      unfold nb076AlphaDummy030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0023 m n)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                    ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                    ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                    ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                    ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                    ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
                                    ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy018) from
                      (by
                        unfold nb076AlphaDummy018;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
                    (show m ≠ (nb076AlphaDummy020 m n) from (by
                        unfold nb076AlphaDummy020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))))
                    (TAlphaVar.there
                      (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy017) from (by
                          unfold nb076AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0014) 0))))
                      (show m ≠ (nb076AlphaDummy019 m n) from (by
                          unfold nb076AlphaDummy019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
                      (TAlphaVar.there
                        (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy023) from (by
                            unfold nb076AlphaDummy023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0018) 0))))
                        (show m ≠ (nb076AlphaDummy024 m n) from (by
                            unfold nb076AlphaDummy024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0019 m n) 0))))
                        (TAlphaVar.there
                          (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy021) from (by
                              unfold nb076AlphaDummy021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0015) 0))))
                          (show m ≠ (nb076AlphaDummy022 m n) from (by
                              unfold nb076AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0017 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy010) from (by
                                unfold nb076AlphaDummy010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0008) 1))))
                            (show m ≠ (nb076AlphaDummy012 g m n a b) from (by
                                unfold nb076AlphaDummy012;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0010 g m n a b)
                                        1)))) (TAlphaVar.there
                              (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy009) from (by
                                  unfold nb076AlphaDummy009;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0008) 0))))
                              (show m ≠ (nb076AlphaDummy011 g m n a b) from (by
                                  unfold nb076AlphaDummy011;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb076_support_mem_0010 g m n a b) 0))))
                              (TAlphaVar.there
                                (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy015) from (by
                                    unfold nb076AlphaDummy015;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0012) 0))))
                                (show m ≠ (nb076AlphaDummy016 g m n a b) from (by
                                    unfold nb076AlphaDummy016;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb076_support_mem_0013 g m n a b) 0))))
                                (TAlphaVar.there
                                  (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy013) from
                                    (by
                                      unfold nb076AlphaDummy013;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0009)
                                              0))))
                                  (show m ≠ (nb076AlphaDummy014 g m n a b) from (by
                                      unfold nb076AlphaDummy014;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0011 g m n a b) 0))))
                                  (TAlphaVar.there (show
                                      (nb076AlphaDummy003) ≠ (nb076AlphaDummy005) from (by
                                        unfold nb076AlphaDummy005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0006)
                                                0))))
                                    (show m ≠ (nb076AlphaDummy006 g m n a b) from (by
                                        unfold nb076AlphaDummy006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0007 g m n a b) 0))))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_m_n (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb076AlphaDummy003))).fv ∪
                        ((Class.cv (nb076AlphaDummy004))).fv) (by decide))
                    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy025) from (by
                                unfold nb076AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 0)))) (show
                              (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy027 m n) from (by
                                unfold nb076AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                            (TAlphaVar.there
                              (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy026) from (by
                                  unfold nb076AlphaDummy026;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                                (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy028 m n) from
                                (by
                                  unfold nb076AlphaDummy028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0021 m n)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076AlphaDummy018))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076AlphaDummy020 m n))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy025) ≠ (nb076AlphaDummy032) from (by
          unfold nb076AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy035 m n) from (by
          unfold nb076AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy031)
        from (by
          unfold nb076AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy034 m n) from (by
          unfold nb076AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029)
        from (by
          unfold nb076AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022)
                  0)))) (show (nb076AlphaDummy027 m n) ≠ (nb076AlphaDummy030 m n) from (by
          unfold nb076AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)), ((nb076AlphaDummy017),
        (nb076AlphaDummy019 m n)), ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
        ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠
        (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)), ((nb076AlphaDummy017),
        (nb076AlphaDummy019 m n)), ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
        ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy027 m
        n))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043) from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043)
        from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠
        (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from
                                        (by
                                          unfold nb076AlphaDummy029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0022)
                                                  0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy030 m n) from (by
                                          unfold nb076AlphaDummy030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0023 m n) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                      ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                      ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                      ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                      ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                      ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
                                      ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                      ((nb076AlphaDummy010),
                                        (nb076AlphaDummy012 g m n a b)),
                                      ((nb076AlphaDummy009),
                                        (nb076AlphaDummy011 g m n a b)),
                                      ((nb076AlphaDummy015),
                                        (nb076AlphaDummy016 g m n a b)),
                                      ((nb076AlphaDummy013),
                                        (nb076AlphaDummy014 g m n a b)),
                                      ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from
                                        (by
                                          unfold nb076AlphaDummy029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0022)
                                                  0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy030 m n) from (by
                                          unfold nb076AlphaDummy030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0023 m n) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                      ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                      ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                      ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                      ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                      ((nb076AlphaDummy023), (nb076AlphaDummy024 m n)),
                                      ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                      ((nb076AlphaDummy010),
                                        (nb076AlphaDummy012 g m n a b)),
                                      ((nb076AlphaDummy009),
                                        (nb076AlphaDummy011 g m n a b)),
                                      ((nb076AlphaDummy015),
                                        (nb076AlphaDummy016 g m n a b)),
                                      ((nb076AlphaDummy013),
                                        (nb076AlphaDummy014 g m n a b)),
                                      ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0001`. -/
@[expose]
noncomputable def nb076SplitAlpha0001 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076AlphaDummy049), (nb076AlphaDummy050 m n)),
        ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
        ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
        ((nb076AlphaDummy047), (nb076AlphaDummy048 m n)),
        ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
        ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)),
        ((nb076AlphaDummy009), (nb076AlphaDummy011 g m n a b)),
        ((nb076AlphaDummy015), (nb076AlphaDummy016 g m n a b)),
        ((nb076AlphaDummy013), (nb076AlphaDummy014 g m n a b)),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy049))
          (synCcompl (synCphi (Class.cv (nb076AlphaDummy018))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy049)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy050 m n))
          (synCcompl (synCphi (Class.cv (nb076AlphaDummy020 m n))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy050 m n))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy025) from (by
                              unfold nb076AlphaDummy025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0020) 0))))
                          (show (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy027 m n) from
                            (by
                              unfold nb076AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy026) from (by
                                unfold nb076AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                              (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy028 m n) from (by
                                unfold nb076AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 1))))
                            (TAlphaVar.there
                              (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy051) from (by
                                  unfold nb076AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0058) 0)))) (show
                                (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy052 m n) from
                                (by
                                  unfold nb076AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0059 m n)
                                          0)))) (TAlphaVar.there
                                (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy049) from (by
                                    unfold nb076AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0056) 0)))) (show
                                  (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy050 m n) from
                                  (by
                                    unfold nb076AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0057 m n)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076AlphaDummy018))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076AlphaDummy020 m n))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy032) from (by
          unfold nb076AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy035 m n) from (by
          unfold nb076AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy025) ≠ (nb076AlphaDummy031) from (by
          unfold nb076AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy034 m n) from (by
          unfold nb076AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029)
        from (by
          unfold nb076AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy030 m n) from (by
          unfold nb076AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)), ((nb076AlphaDummy049),
        (nb076AlphaDummy050 m n)), ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
        ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)), ((nb076AlphaDummy047),
        (nb076AlphaDummy048 m n)), ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
        ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠
        (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)), ((nb076AlphaDummy049),
        (nb076AlphaDummy050 m n)), ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
        ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)), ((nb076AlphaDummy047),
        (nb076AlphaDummy048 m n)), ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
        ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy027 m
        n))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043) from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043)
        from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠
        (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                    ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                    ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                    ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)),
                                    ((nb076AlphaDummy049), (nb076AlphaDummy050 m n)),
                                    ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                    ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                    ((nb076AlphaDummy047), (nb076AlphaDummy048 m n)),
                                    ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from
                                    (by
                                      unfold nb076AlphaDummy029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0022)
                                              0)))) (show (nb076AlphaDummy027 m n) ≠
                                      (nb076AlphaDummy030 m n) from (by
                                      unfold nb076AlphaDummy030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0023 m n)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                    ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                    ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                    ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)),
                                    ((nb076AlphaDummy049), (nb076AlphaDummy050 m n)),
                                    ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                    ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                    ((nb076AlphaDummy047), (nb076AlphaDummy048 m n)),
                                    ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy025) from (by
                              unfold nb076AlphaDummy025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0020) 0))))
                          (show (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy027 m n) from
                            (by
                              unfold nb076AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy026) from (by
                                unfold nb076AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                              (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy028 m n) from (by
                                unfold nb076AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 1))))
                            (TAlphaVar.there
                              (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy051) from (by
                                  unfold nb076AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0058) 0)))) (show
                                (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy052 m n) from
                                (by
                                  unfold nb076AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0059 m n)
                                          0)))) (TAlphaVar.there
                                (show (nb076AlphaDummy018) ≠ (nb076AlphaDummy049) from (by
                                    unfold nb076AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0056) 0)))) (show
                                  (nb076AlphaDummy020 m n) ≠ (nb076AlphaDummy050 m n) from
                                  (by
                                    unfold nb076AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0057 m n)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076AlphaDummy018))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076AlphaDummy020 m n))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy032) from (by
          unfold nb076AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy035 m n) from (by
          unfold nb076AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy025) ≠ (nb076AlphaDummy031) from (by
          unfold nb076AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy034 m n) from (by
          unfold nb076AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029)
        from (by
          unfold nb076AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022) 0)))) (show (nb076AlphaDummy027 m n) ≠
        (nb076AlphaDummy030 m n) from (by
          unfold nb076AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)), ((nb076AlphaDummy049),
        (nb076AlphaDummy050 m n)), ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
        ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)), ((nb076AlphaDummy047),
        (nb076AlphaDummy048 m n)), ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
        ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠
        (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy039) from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy039)
        from (by
          unfold
            nb076AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy040 m n) from (by
          unfold
            nb076AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy037)
        from (by
          unfold
            nb076AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy038 m n) from (by
          unfold
            nb076AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy033), (nb076AlphaDummy036 m n)), ((nb076AlphaDummy032),
        (nb076AlphaDummy035 m n)), ((nb076AlphaDummy031), (nb076AlphaDummy034 m n)),
        ((nb076AlphaDummy029), (nb076AlphaDummy030 m n)), ((nb076AlphaDummy025),
        (nb076AlphaDummy027 m n)), ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
        ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)), ((nb076AlphaDummy049),
        (nb076AlphaDummy050 m n)), ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
        ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)), ((nb076AlphaDummy047),
        (nb076AlphaDummy048 m n)), ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
        ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy027 m
        n))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043) from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy043)
        from (by
          unfold
            nb076AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy044 m n) from (by
          unfold
            nb076AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy032) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076AlphaDummy035 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy027 m n))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy033) ≠
        (nb076AlphaDummy045) from (by
          unfold
            nb076AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy046 m n) from (by
          unfold
            nb076AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy033) ≠ (nb076AlphaDummy041)
        from (by
          unfold
            nb076AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076AlphaDummy036 m n) ≠ (nb076AlphaDummy042 m n) from (by
          unfold
            nb076AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                    ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                    ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                    ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)),
                                    ((nb076AlphaDummy049), (nb076AlphaDummy050 m n)),
                                    ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                    ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                    ((nb076AlphaDummy047), (nb076AlphaDummy048 m n)),
                                    ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from
                                    (by
                                      unfold nb076AlphaDummy029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0022)
                                              0)))) (show (nb076AlphaDummy027 m n) ≠
                                      (nb076AlphaDummy030 m n) from (by
                                      unfold nb076AlphaDummy030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0023 m n)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy025) ≠ (nb076AlphaDummy029) from (by
                                        unfold nb076AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076AlphaDummy027 m n) ≠
                                        (nb076AlphaDummy030 m n) from (by
                                        unfold nb076AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy029), (nb076AlphaDummy030 m n)),
                                    ((nb076AlphaDummy025), (nb076AlphaDummy027 m n)),
                                    ((nb076AlphaDummy026), (nb076AlphaDummy028 m n)),
                                    ((nb076AlphaDummy051), (nb076AlphaDummy052 m n)),
                                    ((nb076AlphaDummy049), (nb076AlphaDummy050 m n)),
                                    ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
                                    ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
                                    ((nb076AlphaDummy047), (nb076AlphaDummy048 m n)),
                                    ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb076AlphaDummy049), (nb076AlphaDummy050 m n)),
            ((nb076AlphaDummy018), (nb076AlphaDummy020 m n)),
            ((nb076AlphaDummy017), (nb076AlphaDummy019 m n)),
            ((nb076AlphaDummy047), (nb076AlphaDummy048 m n)),
            ((nb076AlphaDummy021), (nb076AlphaDummy022 m n)),
            ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)),
            ((nb076AlphaDummy009), (nb076AlphaDummy011 g m n a b)),
            ((nb076AlphaDummy015), (nb076AlphaDummy016 g m n a b)),
            ((nb076AlphaDummy013), (nb076AlphaDummy014 g m n a b)),
            ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
            ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
            ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
