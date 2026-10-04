/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part032`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0000`. -/
@[expose]
noncomputable def nb078SplitAlpha0000 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
        ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy023))
          (Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy023)) (Class.cab (nb078AlphaDummy017)
              (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy017))
                  (synCphi (Class.cv (nb078AlphaDummy018)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy024 f))
          (Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy024 f))
            (Class.cab (nb078AlphaDummy019 f)
              (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                  (synCphi (Class.cv (nb078AlphaDummy020 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy018) from
                    (by
                      unfold nb078AlphaDummy018;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
                  (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy020 f) from (by
                      unfold nb078AlphaDummy020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy017) from
                      (by
                        unfold nb078AlphaDummy017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))))
                    (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy019 f) from (by
                        unfold nb078AlphaDummy019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0006 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy023) from (by
                          unfold nb078AlphaDummy023;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0008) 0))))
                      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy024 f) from (by
                          unfold nb078AlphaDummy024;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0009 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy021) from (by
                            unfold nb078AlphaDummy021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0005) 0))))
                        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy022 f) from (by
                            unfold nb078AlphaDummy022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0007 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078AlphaDummy009))).fv ∪
                      ((Class.cv (nb078AlphaDummy010))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy012 f))).fv ∪
                      ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy025) from (by
                              unfold nb078AlphaDummy025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                          (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy027 f) from (by
                              unfold nb078AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy026) from (by
                                unfold nb078AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                            (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy028 f) from (by
                                unfold nb078AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy018))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy020 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy032) from (by
          unfold nb078AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy035 f) from (by
          unfold nb078AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy031) from (by
          unfold nb078AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy034 f) from (by
          unfold nb078AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
          unfold nb078AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy030 f) from (by
          unfold nb078AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy018), (nb078AlphaDummy020 f)), ((nb078AlphaDummy017),
        (nb078AlphaDummy019 f)), ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
        ((nb078AlphaDummy021), (nb078AlphaDummy022 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy018), (nb078AlphaDummy020 f)), ((nb078AlphaDummy017),
        (nb078AlphaDummy019 f)), ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
        ((nb078AlphaDummy021), (nb078AlphaDummy022 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy027
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043) from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043)
        from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠
        (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                    ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                    ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                    ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                    ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                    ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
                                    ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from
                                    (by
                                      unfold nb078AlphaDummy029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0012)
                                              0)))) (show
                                    (nb078AlphaDummy027 f) ≠ (nb078AlphaDummy030 f) from
                                    (by
                                      unfold nb078AlphaDummy030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                    ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                    ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                    ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                    ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                    ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
                                    ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy018) from
                      (by
                        unfold nb078AlphaDummy018;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
                    (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy020 f) from (by
                        unfold nb078AlphaDummy020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0006 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy017) from (by
                          unfold nb078AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0004) 0))))
                      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy019 f) from (by
                          unfold nb078AlphaDummy019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0006 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy023) from (by
                            unfold nb078AlphaDummy023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0008) 0))))
                        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy024 f) from (by
                            unfold nb078AlphaDummy024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0009 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy021) from (by
                              unfold nb078AlphaDummy021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0005) 0))))
                          (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy022 f) from (by
                              unfold nb078AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0007 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy009))).fv ∪
                        ((Class.cv (nb078AlphaDummy010))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy012 f))).fv ∪
                        ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy025) from (by
                                unfold nb078AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                            (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy027 f) from (by
                                unfold nb078AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy026) from (by
                                  unfold nb078AlphaDummy026;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                              (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy028 f) from
                                (by
                                  unfold nb078AlphaDummy028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy018))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy020 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy032) from (by
          unfold nb078AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy035 f) from (by
          unfold nb078AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy031) from (by
          unfold nb078AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy034 f) from (by
          unfold nb078AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy029)
        from (by
          unfold nb078AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012)
                  0)))) (show (nb078AlphaDummy027 f) ≠ (nb078AlphaDummy030 f) from (by
          unfold nb078AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy018), (nb078AlphaDummy020 f)), ((nb078AlphaDummy017),
        (nb078AlphaDummy019 f)), ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
        ((nb078AlphaDummy021), (nb078AlphaDummy022 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy018), (nb078AlphaDummy020 f)), ((nb078AlphaDummy017),
        (nb078AlphaDummy019 f)), ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
        ((nb078AlphaDummy021), (nb078AlphaDummy022 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy027
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043) from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043)
        from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠
        (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from
                                        (by
                                          unfold nb078AlphaDummy029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0012)
                                                  0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy030 f) from (by
                                          unfold nb078AlphaDummy030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                      ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                      ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                      ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                      ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                      ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
                                      ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                      ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from
                                        (by
                                          unfold nb078AlphaDummy029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0012)
                                                  0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy030 f) from (by
                                          unfold nb078AlphaDummy030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                      ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                      ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                      ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                      ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                      ((nb078AlphaDummy023), (nb078AlphaDummy024 f)),
                                      ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                      ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part033`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0001`. -/
@[expose]
noncomputable def nb078SplitAlpha0001 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy049), (nb078AlphaDummy050 f)),
        ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
        ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
        ((nb078AlphaDummy047), (nb078AlphaDummy048 f)),
        ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy049))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy018))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy049)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy050 f))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy020 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy050 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy025) from (by
                              unfold nb078AlphaDummy025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                          (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy027 f) from (by
                              unfold nb078AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy026) from (by
                                unfold nb078AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                            (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy028 f) from (by
                                unfold nb078AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy051) from (by
                                  unfold nb078AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0040) 0))))
                              (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy052 f) from
                                (by
                                  unfold nb078AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0041 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy049) from (by
                                    unfold nb078AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0038) 0)))) (show
                                  (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy050 f) from (by
                                    unfold nb078AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0039 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy018))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy020 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy032) from (by
          unfold nb078AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy035 f) from (by
          unfold nb078AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy031) from (by
          unfold nb078AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy034 f) from (by
          unfold nb078AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
          unfold nb078AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy030 f) from (by
          unfold nb078AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy051), (nb078AlphaDummy052 f)), ((nb078AlphaDummy049),
        (nb078AlphaDummy050 f)), ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
        ((nb078AlphaDummy017), (nb078AlphaDummy019 f)), ((nb078AlphaDummy047),
        (nb078AlphaDummy048 f)), ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy051), (nb078AlphaDummy052 f)), ((nb078AlphaDummy049),
        (nb078AlphaDummy050 f)), ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
        ((nb078AlphaDummy017), (nb078AlphaDummy019 f)), ((nb078AlphaDummy047),
        (nb078AlphaDummy048 f)), ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy027
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043) from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043)
        from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠
        (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                    ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                    ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                    ((nb078AlphaDummy051), (nb078AlphaDummy052 f)),
                                    ((nb078AlphaDummy049), (nb078AlphaDummy050 f)),
                                    ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                    ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                    ((nb078AlphaDummy047), (nb078AlphaDummy048 f)),
                                    ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from
                                    (by
                                      unfold nb078AlphaDummy029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0012)
                                              0)))) (show
                                    (nb078AlphaDummy027 f) ≠ (nb078AlphaDummy030 f) from
                                    (by
                                      unfold nb078AlphaDummy030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                    ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                    ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                    ((nb078AlphaDummy051), (nb078AlphaDummy052 f)),
                                    ((nb078AlphaDummy049), (nb078AlphaDummy050 f)),
                                    ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                    ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                    ((nb078AlphaDummy047), (nb078AlphaDummy048 f)),
                                    ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy025) from (by
                              unfold nb078AlphaDummy025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                          (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy027 f) from (by
                              unfold nb078AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy026) from (by
                                unfold nb078AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                            (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy028 f) from (by
                                unfold nb078AlphaDummy028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy051) from (by
                                  unfold nb078AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0040) 0))))
                              (show (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy052 f) from
                                (by
                                  unfold nb078AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0041 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy018) ≠ (nb078AlphaDummy049) from (by
                                    unfold nb078AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0038) 0)))) (show
                                  (nb078AlphaDummy020 f) ≠ (nb078AlphaDummy050 f) from (by
                                    unfold nb078AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0039 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy018))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy020 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy032) from (by
          unfold nb078AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy035 f) from (by
          unfold nb078AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy031) from (by
          unfold nb078AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy034 f) from (by
          unfold nb078AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
          unfold nb078AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012) 0)))) (show (nb078AlphaDummy027 f) ≠
        (nb078AlphaDummy030 f) from (by
          unfold nb078AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy051), (nb078AlphaDummy052 f)), ((nb078AlphaDummy049),
        (nb078AlphaDummy050 f)), ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
        ((nb078AlphaDummy017), (nb078AlphaDummy019 f)), ((nb078AlphaDummy047),
        (nb078AlphaDummy048 f)), ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy039) from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy039)
        from (by
          unfold
            nb078AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy040 f) from (by
          unfold
            nb078AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy037)
        from (by
          unfold
            nb078AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy038 f) from (by
          unfold
            nb078AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy033), (nb078AlphaDummy036 f)), ((nb078AlphaDummy032),
        (nb078AlphaDummy035 f)), ((nb078AlphaDummy031), (nb078AlphaDummy034 f)),
        ((nb078AlphaDummy029), (nb078AlphaDummy030 f)), ((nb078AlphaDummy025),
        (nb078AlphaDummy027 f)), ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
        ((nb078AlphaDummy051), (nb078AlphaDummy052 f)), ((nb078AlphaDummy049),
        (nb078AlphaDummy050 f)), ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
        ((nb078AlphaDummy017), (nb078AlphaDummy019 f)), ((nb078AlphaDummy047),
        (nb078AlphaDummy048 f)), ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy027
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043) from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy043)
        from (by
          unfold
            nb078AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy044 f) from (by
          unfold
            nb078AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy032) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy033) ≠
        (nb078AlphaDummy045) from (by
          unfold
            nb078AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy046 f) from (by
          unfold
            nb078AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy033) ≠ (nb078AlphaDummy041)
        from (by
          unfold
            nb078AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078AlphaDummy036 f) ≠ (nb078AlphaDummy042 f) from (by
          unfold
            nb078AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                    ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                    ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                    ((nb078AlphaDummy051), (nb078AlphaDummy052 f)),
                                    ((nb078AlphaDummy049), (nb078AlphaDummy050 f)),
                                    ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                    ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                    ((nb078AlphaDummy047), (nb078AlphaDummy048 f)),
                                    ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from
                                    (by
                                      unfold nb078AlphaDummy029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0012)
                                              0)))) (show
                                    (nb078AlphaDummy027 f) ≠ (nb078AlphaDummy030 f) from
                                    (by
                                      unfold nb078AlphaDummy030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy025) ≠ (nb078AlphaDummy029) from (by
                                        unfold nb078AlphaDummy029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078AlphaDummy027 f) ≠
                                        (nb078AlphaDummy030 f) from (by
                                        unfold nb078AlphaDummy030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy029), (nb078AlphaDummy030 f)),
                                    ((nb078AlphaDummy025), (nb078AlphaDummy027 f)),
                                    ((nb078AlphaDummy026), (nb078AlphaDummy028 f)),
                                    ((nb078AlphaDummy051), (nb078AlphaDummy052 f)),
                                    ((nb078AlphaDummy049), (nb078AlphaDummy050 f)),
                                    ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
                                    ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
                                    ((nb078AlphaDummy047), (nb078AlphaDummy048 f)),
                                    ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy049), (nb078AlphaDummy050 f)),
            ((nb078AlphaDummy018), (nb078AlphaDummy020 f)),
            ((nb078AlphaDummy017), (nb078AlphaDummy019 f)),
            ((nb078AlphaDummy047), (nb078AlphaDummy048 f)),
            ((nb078AlphaDummy021), (nb078AlphaDummy022 f)),
            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
            ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
            ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part034`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0002`. -/
@[expose]
noncomputable def nb078SplitAlpha0002 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
        ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy059))
          (Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy059)) (Class.cab (nb078AlphaDummy053)
              (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
                (Wff.classEq (Class.cv (nb078AlphaDummy053))
                  (synCphi (Class.cv (nb078AlphaDummy054)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy060 f))
          (Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy060 f))
            (Class.cab (nb078AlphaDummy055 f)
              (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                  (synCphi (Class.cv (nb078AlphaDummy056 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy054) from
                    (by
                      unfold nb078AlphaDummy054;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
                  (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy056 f) from (by
                      unfold nb078AlphaDummy056;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy053) from
                      (by
                        unfold nb078AlphaDummy053;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))))
                    (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy055 f) from (by
                        unfold nb078AlphaDummy055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0044 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy059) from (by
                          unfold nb078AlphaDummy059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0046) 0))))
                      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy060 f) from (by
                          unfold nb078AlphaDummy060;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0047 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy057) from (by
                            unfold nb078AlphaDummy057;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0043) 0))))
                        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy058 f) from (by
                            unfold nb078AlphaDummy058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0045 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy009))).fv ∪
                      ((Class.cv (nb078AlphaDummy011))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy012 f))).fv ∪
                      ((Class.cv (nb078AlphaDummy014 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy061) from (by
                              unfold nb078AlphaDummy061;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0048) 0))))
                          (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy063 f) from (by
                              unfold nb078AlphaDummy063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0049 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy062) from (by
                                unfold nb078AlphaDummy062;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0048) 1))))
                            (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy064 f) from (by
                                unfold nb078AlphaDummy064;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0049 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy054))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy056 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy061) ≠ (nb078AlphaDummy068) from (by
          unfold nb078AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 1)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy071 f) from (by
          unfold nb078AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy067) from (by
          unfold nb078AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy070 f) from (by
          unfold nb078AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from (by
          unfold nb078AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0050) 0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
          unfold nb078AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy054), (nb078AlphaDummy056 f)), ((nb078AlphaDummy053),
        (nb078AlphaDummy055 f)), ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
        ((nb078AlphaDummy057), (nb078AlphaDummy058 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy054), (nb078AlphaDummy056 f)), ((nb078AlphaDummy053),
        (nb078AlphaDummy055 f)), ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
        ((nb078AlphaDummy057), (nb078AlphaDummy058 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy063 f))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠
        (nb078AlphaDummy079) from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy079)
        from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠
        (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from (by
                                        unfold nb078AlphaDummy065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078AlphaDummy063 f) ≠
                                        (nb078AlphaDummy066 f) from (by
                                        unfold nb078AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                    ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                    ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                    ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                    ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                    ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
                                    ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                    (by
                                      unfold nb078AlphaDummy065;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0050)
                                              0)))) (show
                                    (nb078AlphaDummy063 f) ≠ (nb078AlphaDummy066 f) from
                                    (by
                                      unfold nb078AlphaDummy066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from (by
                                        unfold nb078AlphaDummy065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078AlphaDummy063 f) ≠
                                        (nb078AlphaDummy066 f) from (by
                                        unfold nb078AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                    ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                    ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                    ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                    ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                    ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
                                    ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                    ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy054) from
                      (by
                        unfold nb078AlphaDummy054;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
                    (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy056 f) from (by
                        unfold nb078AlphaDummy056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0044 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy053) from (by
                          unfold nb078AlphaDummy053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0042) 0))))
                      (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy055 f) from (by
                          unfold nb078AlphaDummy055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0044 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy059) from (by
                            unfold nb078AlphaDummy059;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0046) 0))))
                        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy060 f) from (by
                            unfold nb078AlphaDummy060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0047 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy057) from (by
                              unfold nb078AlphaDummy057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0043) 0))))
                          (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy058 f) from (by
                              unfold nb078AlphaDummy058;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0045 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb078AlphaDummy000))).fv ∪
                                  ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy009))).fv ∪
                        ((Class.cv (nb078AlphaDummy011))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy012 f))).fv ∪
                        ((Class.cv (nb078AlphaDummy014 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy061) from (by
                                unfold nb078AlphaDummy061;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0048) 0))))
                            (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy063 f) from (by
                                unfold nb078AlphaDummy063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0049 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy062) from (by
                                  unfold nb078AlphaDummy062;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0048) 1))))
                              (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy064 f) from
                                (by
                                  unfold nb078AlphaDummy064;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0049 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy054))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy056 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy068) from (by
          unfold nb078AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 1)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy071 f) from (by
          unfold nb078AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy067) from (by
          unfold nb078AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy070 f) from (by
          unfold nb078AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy061) ≠ (nb078AlphaDummy065)
        from (by
          unfold nb078AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0050)
                  0)))) (show (nb078AlphaDummy063 f) ≠ (nb078AlphaDummy066 f) from (by
          unfold nb078AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy054), (nb078AlphaDummy056 f)), ((nb078AlphaDummy053),
        (nb078AlphaDummy055 f)), ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
        ((nb078AlphaDummy057), (nb078AlphaDummy058 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy054), (nb078AlphaDummy056 f)), ((nb078AlphaDummy053),
        (nb078AlphaDummy055 f)), ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
        ((nb078AlphaDummy057), (nb078AlphaDummy058 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy063
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠
        (nb078AlphaDummy079) from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy079)
        from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠
        (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                        (by
                                          unfold nb078AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
                                          unfold nb078AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                      ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                      ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                      ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                      ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                      ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
                                      ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                      ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from (by
                                        unfold nb078AlphaDummy065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078AlphaDummy063 f) ≠
                                        (nb078AlphaDummy066 f) from (by
                                        unfold nb078AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                        (by
                                          unfold nb078AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
                                          unfold nb078AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                      ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                      ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                      ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                      ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                      ((nb078AlphaDummy059), (nb078AlphaDummy060 f)),
                                      ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                      ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
