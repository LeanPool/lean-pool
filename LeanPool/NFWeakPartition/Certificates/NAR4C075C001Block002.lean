/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C075C001Part004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C075C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb075_split_alpha_0002`. -/
@[expose]
noncomputable def nb075SplitAlpha0002 (x : Var) :
    TAlphaWff
      [((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
      (Wff.classEq (Class.cv (nb075AlphaDummy003))
        (synCop (Class.cv (nb075AlphaDummy000)) (Class.cv (nb075AlphaDummy001))))
      (Wff.classEq (Class.cv (nb075AlphaDummy004 x))
        (synCop (Class.cv x) (Class.cv (nb075AlphaDummy002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy003) from (by
              unfold nb075AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0002) 0))))) (Ne.symm
          (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy004 x) from (by
              unfold nb075AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0003 x) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy003) from
              (by
                unfold nb075AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb075AlphaDummy004 x) from (by
                unfold nb075AlphaDummy004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0001 x) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy006) from (by
                                    unfold nb075AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0006) 1))))
                                (show x ≠ (nb075AlphaDummy008 x) from (by
                                    unfold nb075AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy005) from
                                    (by
                                      unfold nb075AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0006)
                                              0)))) (show x ≠ (nb075AlphaDummy007 x) from (by
                                      unfold nb075AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075AlphaDummy000) ≠ (nb075AlphaDummy011) from (by
                                        unfold nb075AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0010)
                                                0)))) (show x ≠ (nb075AlphaDummy012 x) from
                                      (by
                                        unfold nb075AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075AlphaDummy000) ≠ (nb075AlphaDummy009) from
                                        (by
                                          unfold nb075AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0007)
                                                  0)))) (show x ≠ (nb075AlphaDummy010 x) from
                                        (by
                                          unfold nb075AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb075AlphaDummy000) ≠
        (nb075AlphaDummy001) from (by
          unfold nb075AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0004) 0)))) (show x ≠ (nb075AlphaDummy002 x) from (by
          unfold nb075AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb075AlphaDummy000))).fv ∪
                                    ((Class.cv (nb075AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb075AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb075AlphaDummy006) ≠
        (nb075AlphaDummy013) from (by
          unfold nb075AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy015 x) from (by
          unfold nb075AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy014) from (by
          unfold nb075AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 1)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy016 x) from (by
          unfold nb075AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb075AlphaDummy006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy013) ≠
        (nb075AlphaDummy020) from (by
          unfold
            nb075AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  1)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy023 x) from (by
          unfold
            nb075AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy019)
        from (by
          unfold
            nb075AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy022 x) from (by
          unfold
            nb075AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017)
        from (by
          unfold
            nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy018 x) from (by
          unfold
            nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy021), (nb075AlphaDummy024 x)), ((nb075AlphaDummy020),
        (nb075AlphaDummy023 x)), ((nb075AlphaDummy019), (nb075AlphaDummy022 x)),
        ((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy021) ≠
        (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy021) ≠
        (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy021), (nb075AlphaDummy024 x)), ((nb075AlphaDummy020),
        (nb075AlphaDummy023 x)), ((nb075AlphaDummy019), (nb075AlphaDummy022 x)),
        ((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
        (nb075AlphaDummy031) from (by
          unfold
            nb075AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy032 x) from (by
          unfold
            nb075AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
        (nb075AlphaDummy031) from (by
          unfold
            nb075AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy032 x) from (by
          unfold
            nb075AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy033) from (by
          unfold
            nb075AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy034 x) from (by
          unfold
            nb075AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy021) ≠
        (nb075AlphaDummy033) from (by
          unfold
            nb075AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy034 x) from (by
          unfold
            nb075AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017)
        from (by
          unfold nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy018 x) from (by
          unfold nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017) from (by
          unfold nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014) 0)))) (show (nb075AlphaDummy015 x) ≠
        (nb075AlphaDummy018 x) from (by
          unfold nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017)
        from (by
          unfold nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy018 x) from (by
          unfold nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy006) from (by
                                    unfold nb075AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0006) 1))))
                                (show x ≠ (nb075AlphaDummy008 x) from (by
                                    unfold nb075AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy005) from
                                    (by
                                      unfold nb075AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0006)
                                              0)))) (show x ≠ (nb075AlphaDummy007 x) from (by
                                      unfold nb075AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075AlphaDummy000) ≠ (nb075AlphaDummy011) from (by
                                        unfold nb075AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0010)
                                                0)))) (show x ≠ (nb075AlphaDummy012 x) from
                                      (by
                                        unfold nb075AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075AlphaDummy000) ≠ (nb075AlphaDummy009) from
                                        (by
                                          unfold nb075AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0007)
                                                  0)))) (show x ≠ (nb075AlphaDummy010 x) from
                                        (by
                                          unfold nb075AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb075AlphaDummy000) ≠
        (nb075AlphaDummy001) from (by
          unfold nb075AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0004) 0)))) (show x ≠ (nb075AlphaDummy002 x) from (by
          unfold nb075AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb075AlphaDummy000))).fv ∪
                                    ((Class.cv (nb075AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb075AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb075AlphaDummy006) ≠
        (nb075AlphaDummy013) from (by
          unfold nb075AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy015 x) from (by
          unfold nb075AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy014) from (by
          unfold nb075AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 1)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy016 x) from (by
          unfold nb075AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb075AlphaDummy006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy013) ≠
        (nb075AlphaDummy020) from (by
          unfold
            nb075AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  1)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy023 x) from (by
          unfold
            nb075AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy019)
        from (by
          unfold
            nb075AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy022 x) from (by
          unfold
            nb075AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017)
        from (by
          unfold
            nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy018 x) from (by
          unfold
            nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy021), (nb075AlphaDummy024 x)), ((nb075AlphaDummy020),
        (nb075AlphaDummy023 x)), ((nb075AlphaDummy019), (nb075AlphaDummy022 x)),
        ((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy021) ≠
        (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy021) ≠
        (nb075AlphaDummy027) from (by
          unfold
            nb075AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy028 x) from (by
          unfold
            nb075AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy025)
        from (by
          unfold
            nb075AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy026 x) from (by
          unfold
            nb075AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy021), (nb075AlphaDummy024 x)), ((nb075AlphaDummy020),
        (nb075AlphaDummy023 x)), ((nb075AlphaDummy019), (nb075AlphaDummy022 x)),
        ((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
        (nb075AlphaDummy031) from (by
          unfold
            nb075AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy032 x) from (by
          unfold
            nb075AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
        (nb075AlphaDummy031) from (by
          unfold
            nb075AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy032 x) from (by
          unfold
            nb075AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy020) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075AlphaDummy023 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy033) from (by
          unfold
            nb075AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy034 x) from (by
          unfold
            nb075AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy021) ≠
        (nb075AlphaDummy033) from (by
          unfold
            nb075AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy034 x) from (by
          unfold
            nb075AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy021) ≠ (nb075AlphaDummy029)
        from (by
          unfold
            nb075AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075AlphaDummy024 x) ≠ (nb075AlphaDummy030 x) from (by
          unfold
            nb075AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017)
        from (by
          unfold nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy018 x) from (by
          unfold nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017) from (by
          unfold nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014) 0)))) (show (nb075AlphaDummy015 x) ≠
        (nb075AlphaDummy018 x) from (by
          unfold nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy013) ≠ (nb075AlphaDummy017)
        from (by
          unfold nb075AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075AlphaDummy015 x) ≠ (nb075AlphaDummy018 x) from (by
          unfold nb075AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy017), (nb075AlphaDummy018 x)), ((nb075AlphaDummy013),
        (nb075AlphaDummy015 x)), ((nb075AlphaDummy014), (nb075AlphaDummy016 x)),
        ((nb075AlphaDummy006), (nb075AlphaDummy008 x)), ((nb075AlphaDummy005),
        (nb075AlphaDummy007 x)), ((nb075AlphaDummy011), (nb075AlphaDummy012 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb075SplitAlpha0001 x)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C075C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb075_split_alpha_0003`. -/
@[expose]
noncomputable def nb075SplitAlpha0003 (x : Var) :
    TAlphaWff
      [((nb075AlphaDummy046), (nb075AlphaDummy048 x)),
        ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy075), (nb075AlphaDummy076 x)),
        ((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
        ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb075AlphaDummy046))
          (Class.cv (nb075AlphaDummy041))) (Wff.neg
          (Wff.classEq (Class.cv (nb075AlphaDummy045))
            (synCun (synCphi (Class.cv (nb075AlphaDummy046))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb075AlphaDummy048 x))
          (Class.cv (nb075AlphaDummy043 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
            (synCun (synCphi (Class.cv (nb075AlphaDummy048 x))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy046) from (by
              unfold nb075AlphaDummy046;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 1))))
          (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy048 x) from (by
              unfold nb075AlphaDummy048;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 1))))
          (TAlphaVar.there (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy045) from (by
                unfold nb075AlphaDummy045;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 0))))
            (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy047 x) from (by
                unfold nb075AlphaDummy047;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 0))))
            (TAlphaVar.there (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy075) from (by
                  unfold nb075AlphaDummy075;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0076) 0))))
              (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy076 x) from (by
                  unfold nb075AlphaDummy076;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0077 x) 0))))
              (TAlphaVar.there (show (nb075AlphaDummy041) ≠ (nb075AlphaDummy049) from (by
                    unfold nb075AlphaDummy049;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0073) 0))))
                (show (nb075AlphaDummy043 x) ≠ (nb075AlphaDummy050 x) from (by
                    unfold nb075AlphaDummy050;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0075 x) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb075AlphaDummy000))).fv ∪ ((synCvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((synCvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb075AlphaDummy042))).fv ∪
                ((Class.cv (nb075AlphaDummy041))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb075AlphaDummy044 x))).fv ∪
                ((Class.cv (nb075AlphaDummy043 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb075AlphaDummy046) ≠ (nb075AlphaDummy053) from (by
                                        unfold nb075AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                0)))) (show (nb075AlphaDummy048 x) ≠
                                        (nb075AlphaDummy055 x) from (by
                                        unfold nb075AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075AlphaDummy046) ≠ (nb075AlphaDummy054) from
                                        (by
                                          unfold nb075AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0050)
                                                  1)))) (show (nb075AlphaDummy048 x) ≠
        (nb075AlphaDummy056 x) from (by
                                          unfold nb075AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb075AlphaDummy046) ≠
        (nb075AlphaDummy079) from (by
          unfold nb075AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0080) 0)))) (show (nb075AlphaDummy048 x) ≠
        (nb075AlphaDummy080 x) from (by
          unfold nb075AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy046) ≠ (nb075AlphaDummy077) from (by
          unfold nb075AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0078) 0)))) (show (nb075AlphaDummy048 x) ≠
        (nb075AlphaDummy078 x) from (by
          unfold nb075AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb075AlphaDummy046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb075AlphaDummy048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy060) from (by
          unfold nb075AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy063 x) from (by
          unfold nb075AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy059)
        from (by
          unfold nb075AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy062 x) from (by
          unfold nb075AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057)
        from (by
          unfold
            nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy058 x) from (by
          unfold
            nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy079), (nb075AlphaDummy080 x)), ((nb075AlphaDummy077),
        (nb075AlphaDummy078 x)), ((nb075AlphaDummy046), (nb075AlphaDummy048 x)),
        ((nb075AlphaDummy045), (nb075AlphaDummy047 x)), ((nb075AlphaDummy075),
        (nb075AlphaDummy076 x)), ((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
        ((nb075AlphaDummy042), (nb075AlphaDummy044 x)), ((nb075AlphaDummy041),
        (nb075AlphaDummy043 x)), ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x), ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy079), (nb075AlphaDummy080 x)), ((nb075AlphaDummy077),
        (nb075AlphaDummy078 x)), ((nb075AlphaDummy046), (nb075AlphaDummy048 x)),
        ((nb075AlphaDummy045), (nb075AlphaDummy047 x)), ((nb075AlphaDummy075),
        (nb075AlphaDummy076 x)), ((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
        ((nb075AlphaDummy042), (nb075AlphaDummy044 x)), ((nb075AlphaDummy041),
        (nb075AlphaDummy043 x)), ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x), ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057)
        from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057), (nb075AlphaDummy058 x)),
        ((nb075AlphaDummy053), (nb075AlphaDummy055 x)), ((nb075AlphaDummy054),
        (nb075AlphaDummy056 x)), ((nb075AlphaDummy079), (nb075AlphaDummy080 x)),
        ((nb075AlphaDummy077), (nb075AlphaDummy078 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy075), (nb075AlphaDummy076 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057), (nb075AlphaDummy058 x)),
        ((nb075AlphaDummy053), (nb075AlphaDummy055 x)), ((nb075AlphaDummy054),
        (nb075AlphaDummy056 x)), ((nb075AlphaDummy079), (nb075AlphaDummy080 x)),
        ((nb075AlphaDummy077), (nb075AlphaDummy078 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy075), (nb075AlphaDummy076 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb075AlphaDummy046) ≠ (nb075AlphaDummy053) from (by
                                        unfold nb075AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                0)))) (show (nb075AlphaDummy048 x) ≠
                                        (nb075AlphaDummy055 x) from (by
                                        unfold nb075AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075AlphaDummy046) ≠ (nb075AlphaDummy054) from
                                        (by
                                          unfold nb075AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0050)
                                                  1)))) (show (nb075AlphaDummy048 x) ≠
        (nb075AlphaDummy056 x) from (by
                                          unfold nb075AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb075AlphaDummy046) ≠
        (nb075AlphaDummy079) from (by
          unfold nb075AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0080) 0)))) (show (nb075AlphaDummy048 x) ≠
        (nb075AlphaDummy080 x) from (by
          unfold nb075AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy046) ≠ (nb075AlphaDummy077) from (by
          unfold nb075AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0078) 0)))) (show (nb075AlphaDummy048 x) ≠
        (nb075AlphaDummy078 x) from (by
          unfold nb075AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb075AlphaDummy046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb075AlphaDummy048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy060) from (by
          unfold nb075AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy063 x) from (by
          unfold nb075AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy059)
        from (by
          unfold nb075AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy062 x) from (by
          unfold nb075AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057)
        from (by
          unfold
            nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy058 x) from (by
          unfold
            nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy079), (nb075AlphaDummy080 x)), ((nb075AlphaDummy077),
        (nb075AlphaDummy078 x)), ((nb075AlphaDummy046), (nb075AlphaDummy048 x)),
        ((nb075AlphaDummy045), (nb075AlphaDummy047 x)), ((nb075AlphaDummy075),
        (nb075AlphaDummy076 x)), ((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
        ((nb075AlphaDummy042), (nb075AlphaDummy044 x)), ((nb075AlphaDummy041),
        (nb075AlphaDummy043 x)), ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x), ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy079), (nb075AlphaDummy080 x)), ((nb075AlphaDummy077),
        (nb075AlphaDummy078 x)), ((nb075AlphaDummy046), (nb075AlphaDummy048 x)),
        ((nb075AlphaDummy045), (nb075AlphaDummy047 x)), ((nb075AlphaDummy075),
        (nb075AlphaDummy076 x)), ((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
        ((nb075AlphaDummy042), (nb075AlphaDummy044 x)), ((nb075AlphaDummy041),
        (nb075AlphaDummy043 x)), ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x), ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057)
        from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057), (nb075AlphaDummy058 x)),
        ((nb075AlphaDummy053), (nb075AlphaDummy055 x)), ((nb075AlphaDummy054),
        (nb075AlphaDummy056 x)), ((nb075AlphaDummy079), (nb075AlphaDummy080 x)),
        ((nb075AlphaDummy077), (nb075AlphaDummy078 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy075), (nb075AlphaDummy076 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057), (nb075AlphaDummy058 x)),
        ((nb075AlphaDummy053), (nb075AlphaDummy055 x)), ((nb075AlphaDummy054),
        (nb075AlphaDummy056 x)), ((nb075AlphaDummy079), (nb075AlphaDummy080 x)),
        ((nb075AlphaDummy077), (nb075AlphaDummy078 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy075), (nb075AlphaDummy076 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb075AlphaDummy077), (nb075AlphaDummy078 x)),
                    ((nb075AlphaDummy046), (nb075AlphaDummy048 x)),
                    ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
                    ((nb075AlphaDummy075), (nb075AlphaDummy076 x)),
                    ((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
                    ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
                    ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
                    ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
                    ((nb075AlphaDummy000), x),
                    ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C075C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb075_split_alpha_0004`. -/
@[expose]
noncomputable def nb075SplitAlpha0004 (x : Var) :
    TAlphaWff
      [((nb075AlphaDummy049), (nb075AlphaDummy050 x)),
        ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb075AlphaDummy049)) (synCcompl
            (Class.cab (nb075AlphaDummy045)
              (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy042))
                (Wff.classEq (Class.cv (nb075AlphaDummy045))
                  (synCphi (Class.cv (nb075AlphaDummy046)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb075AlphaDummy049)) (synCcompl
              (Class.cab (nb075AlphaDummy045)
                (synWrex (nb075AlphaDummy046) (Class.cv (nb075AlphaDummy041))
                  (Wff.classEq (Class.cv (nb075AlphaDummy045))
                    (synCun (synCphi (Class.cv (nb075AlphaDummy046)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb075AlphaDummy050 x)) (synCcompl
            (Class.cab (nb075AlphaDummy047 x)
              (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                  (synCphi (Class.cv (nb075AlphaDummy048 x)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb075AlphaDummy050 x)) (synCcompl
              (Class.cab (nb075AlphaDummy047 x)
                (synWrex (nb075AlphaDummy048 x) (Class.cv (nb075AlphaDummy043 x))
                  (Wff.classEq (Class.cv (nb075AlphaDummy047 x))
                    (synCun (synCphi (Class.cv (nb075AlphaDummy048 x)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy046) from (by
                              unfold nb075AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0044) 1))))
                          (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy048 x) from (by
                              unfold nb075AlphaDummy048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy045) from (by
                                unfold nb075AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0044) 0))))
                            (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy047 x) from (by
                                unfold nb075AlphaDummy047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy051) from (by
                                  unfold nb075AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0048) 0))))
                              (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy052 x) from
                                (by
                                  unfold nb075AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy049) from (by
                                    unfold nb075AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0045) 0)))) (show
                                  (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy050 x) from (by
                                    unfold nb075AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb075AlphaDummy042))).fv ∪
                              ((Class.cv (nb075AlphaDummy041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb075AlphaDummy044 x))).fv ∪
                              ((Class.cv (nb075AlphaDummy043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb075AlphaDummy046) ≠ (nb075AlphaDummy053) from
                                    (by
                                      unfold nb075AlphaDummy053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0050)
                                              0)))) (show
                                    (nb075AlphaDummy048 x) ≠ (nb075AlphaDummy055 x) from
                                    (by
                                      unfold nb075AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075AlphaDummy046) ≠ (nb075AlphaDummy054) from (by
                                        unfold nb075AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                1)))) (show (nb075AlphaDummy048 x) ≠
                                        (nb075AlphaDummy056 x) from (by
                                        unfold nb075AlphaDummy056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb075AlphaDummy046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb075AlphaDummy048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy060) from (by
          unfold nb075AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy063 x) from (by
          unfold nb075AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy059)
        from (by
          unfold nb075AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy062 x) from (by
          unfold nb075AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057)
        from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy046), (nb075AlphaDummy048 x)), ((nb075AlphaDummy045),
        (nb075AlphaDummy047 x)), ((nb075AlphaDummy051), (nb075AlphaDummy052 x)),
        ((nb075AlphaDummy049), (nb075AlphaDummy050 x)), ((nb075AlphaDummy042),
        (nb075AlphaDummy044 x)), ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy046), (nb075AlphaDummy048 x)), ((nb075AlphaDummy045),
        (nb075AlphaDummy047 x)), ((nb075AlphaDummy051), (nb075AlphaDummy052 x)),
        ((nb075AlphaDummy049), (nb075AlphaDummy050 x)), ((nb075AlphaDummy042),
        (nb075AlphaDummy044 x)), ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057),
        (nb075AlphaDummy058 x)), ((nb075AlphaDummy053), (nb075AlphaDummy055 x)),
        ((nb075AlphaDummy054), (nb075AlphaDummy056 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy051), (nb075AlphaDummy052 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057),
        (nb075AlphaDummy058 x)), ((nb075AlphaDummy053), (nb075AlphaDummy055 x)),
        ((nb075AlphaDummy054), (nb075AlphaDummy056 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy051), (nb075AlphaDummy052 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy046) from (by
                              unfold nb075AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0044) 1))))
                          (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy048 x) from (by
                              unfold nb075AlphaDummy048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy045) from (by
                                unfold nb075AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0044) 0))))
                            (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy047 x) from (by
                                unfold nb075AlphaDummy047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy051) from (by
                                  unfold nb075AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0048) 0))))
                              (show (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy052 x) from
                                (by
                                  unfold nb075AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb075AlphaDummy042) ≠ (nb075AlphaDummy049) from (by
                                    unfold nb075AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0045) 0)))) (show
                                  (nb075AlphaDummy044 x) ≠ (nb075AlphaDummy050 x) from (by
                                    unfold nb075AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb075AlphaDummy042))).fv ∪
                              ((Class.cv (nb075AlphaDummy041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb075AlphaDummy044 x))).fv ∪
                              ((Class.cv (nb075AlphaDummy043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb075AlphaDummy046) ≠ (nb075AlphaDummy053) from
                                    (by
                                      unfold nb075AlphaDummy053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0050)
                                              0)))) (show
                                    (nb075AlphaDummy048 x) ≠ (nb075AlphaDummy055 x) from
                                    (by
                                      unfold nb075AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075AlphaDummy046) ≠ (nb075AlphaDummy054) from (by
                                        unfold nb075AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                1)))) (show (nb075AlphaDummy048 x) ≠
                                        (nb075AlphaDummy056 x) from (by
                                        unfold nb075AlphaDummy056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb075AlphaDummy046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb075AlphaDummy048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy060) from (by
          unfold nb075AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy063 x) from (by
          unfold nb075AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy059)
        from (by
          unfold nb075AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy062 x) from (by
          unfold nb075AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy053) ≠ (nb075AlphaDummy057)
        from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075AlphaDummy055 x) ≠ (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy046), (nb075AlphaDummy048 x)), ((nb075AlphaDummy045),
        (nb075AlphaDummy047 x)), ((nb075AlphaDummy051), (nb075AlphaDummy052 x)),
        ((nb075AlphaDummy049), (nb075AlphaDummy050 x)), ((nb075AlphaDummy042),
        (nb075AlphaDummy044 x)), ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy067) from (by
          unfold
            nb075AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy068 x) from (by
          unfold
            nb075AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy065)
        from (by
          unfold
            nb075AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy066 x) from (by
          unfold
            nb075AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb075AlphaDummy061), (nb075AlphaDummy064 x)), ((nb075AlphaDummy060),
        (nb075AlphaDummy063 x)), ((nb075AlphaDummy059), (nb075AlphaDummy062 x)),
        ((nb075AlphaDummy057), (nb075AlphaDummy058 x)), ((nb075AlphaDummy053),
        (nb075AlphaDummy055 x)), ((nb075AlphaDummy054), (nb075AlphaDummy056 x)),
        ((nb075AlphaDummy046), (nb075AlphaDummy048 x)), ((nb075AlphaDummy045),
        (nb075AlphaDummy047 x)), ((nb075AlphaDummy051), (nb075AlphaDummy052 x)),
        ((nb075AlphaDummy049), (nb075AlphaDummy050 x)), ((nb075AlphaDummy042),
        (nb075AlphaDummy044 x)), ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy060) ≠
        (nb075AlphaDummy071) from (by
          unfold
            nb075AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy072 x) from (by
          unfold
            nb075AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy060) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075AlphaDummy063 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy061) ≠
        (nb075AlphaDummy073) from (by
          unfold
            nb075AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy074 x) from (by
          unfold
            nb075AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075AlphaDummy061) ≠ (nb075AlphaDummy069)
        from (by
          unfold
            nb075AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075AlphaDummy064 x) ≠ (nb075AlphaDummy070 x) from (by
          unfold
            nb075AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057),
        (nb075AlphaDummy058 x)), ((nb075AlphaDummy053), (nb075AlphaDummy055 x)),
        ((nb075AlphaDummy054), (nb075AlphaDummy056 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy051), (nb075AlphaDummy052 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy053) ≠ (nb075AlphaDummy057) from (by
          unfold nb075AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075AlphaDummy055 x) ≠
        (nb075AlphaDummy058 x) from (by
          unfold nb075AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb075AlphaDummy057),
        (nb075AlphaDummy058 x)), ((nb075AlphaDummy053), (nb075AlphaDummy055 x)),
        ((nb075AlphaDummy054), (nb075AlphaDummy056 x)), ((nb075AlphaDummy046),
        (nb075AlphaDummy048 x)), ((nb075AlphaDummy045), (nb075AlphaDummy047 x)),
        ((nb075AlphaDummy051), (nb075AlphaDummy052 x)), ((nb075AlphaDummy049),
        (nb075AlphaDummy050 x)), ((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
        ((nb075AlphaDummy041), (nb075AlphaDummy043 x)), ((nb075AlphaDummy001),
        (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x), ((nb075AlphaDummy003),
        (nb075AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb075SplitAlpha0003 x)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb075SplitAlpha0003 x)))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_ranfn`. -/
@[expose]
noncomputable def nominalDfRanfn (x : Var) :
    Nominal.NPrf (.classEq (synCranfn) (synCmpt x (synCvv) (synCrn (.cv x)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb075SplitAlpha0002 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy001) from (by
                          unfold nb075AlphaDummy001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0004) 0))))
                      (show x ≠ (nb075AlphaDummy002 x) from (by
                          unfold nb075AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0005 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
                      ((nb075AlphaDummy000), x),
                      ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
                    (synCvv) (by simp only [fv_syn_cvv])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb075AlphaDummy042), (nb075AlphaDummy044 x)),
                              ((nb075AlphaDummy041), (nb075AlphaDummy043 x)),
                              ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
                              ((nb075AlphaDummy000), x),
                              ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
                            (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                          (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.neg (nb075SplitAlpha0004 x))))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy042) from (by
                                  unfold nb075AlphaDummy042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0082) 1))))
                              (show x ≠ (nb075AlphaDummy044 x) from (by
                                  unfold nb075AlphaDummy044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0083 x) 1))))
                              (TAlphaVar.there
                                (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy041) from (by
                                    unfold nb075AlphaDummy041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0082) 0))))
                                (show x ≠ (nb075AlphaDummy043 x) from (by
                                    unfold nb075AlphaDummy043;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0083 x)
                                            0)))) (TAlphaVar.there
                                  (show (nb075AlphaDummy000) ≠ (nb075AlphaDummy001) from
                                    (by
                                      unfold nb075AlphaDummy001;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0004)
                                              0)))) (show x ≠ (nb075AlphaDummy002 x) from (by
                                      unfold nb075AlphaDummy002;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0005 x)
                                              0)))) (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
