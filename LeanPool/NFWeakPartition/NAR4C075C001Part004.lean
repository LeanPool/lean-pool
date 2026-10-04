/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C075C001Block001

/-! NF weak partition development: NAR4C075C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb075_split_alpha_0000`. -/
@[expose]
noncomputable def nb075SplitAlpha0000 (x : Var) :
    TAlphaWff
      [((nb075AlphaDummy035), (nb075AlphaDummy036 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
      (Wff.neg (Wff.classMem (Class.cv (nb075AlphaDummy035))
          (Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006))) (synCsn (synC0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb075AlphaDummy036 x))
          (Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy006) from
                    (by
                      unfold nb075AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 1))))
                  (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy008 x) from (by
                      unfold nb075AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 1))))
                  (TAlphaVar.there (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy005) from
                      (by
                        unfold nb075AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 0))))
                    (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy007 x) from (by
                        unfold nb075AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb075_support_mem_0036 x) 0)))) (TAlphaVar.there
                      (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy035) from (by
                          unfold nb075AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0038) 0))))
                      (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy036 x) from (by
                          unfold nb075AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0039 x) 0))))
                      (TAlphaVar.there
                        (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy009) from (by
                            unfold nb075AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb075_support_mem_0035) 0))))
                        (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy010 x) from (by
                            unfold nb075AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb075_support_mem_0037 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb075AlphaDummy000))).fv ∪
                      ((Class.cv (nb075AlphaDummy001))).fv) (by decide)) (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy039) from (by
          unfold nb075AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0042) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy040 x) from (by
          unfold nb075AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy037) from (by
          unfold nb075AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0040) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy038 x) from (by
          unfold nb075AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy013) ≠ (nb075AlphaDummy017) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy039) from (by
          unfold nb075AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0042) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy040 x) from (by
          unfold nb075AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy037) from (by
          unfold nb075AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0040) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy038 x) from (by
          unfold nb075AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy013) ≠ (nb075AlphaDummy017) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb075AlphaDummy037), (nb075AlphaDummy038 x)),
                          ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
                          ((nb075AlphaDummy005), (nb075AlphaDummy007 x)),
                          ((nb075AlphaDummy035), (nb075AlphaDummy036 x)),
                          ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
                          ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
                          ((nb075AlphaDummy000), x),
                          ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb075_split_alpha_0001`. -/
@[expose]
noncomputable def nb075SplitAlpha0001 (x : Var) :
    TAlphaWff
      [((nb075AlphaDummy035), (nb075AlphaDummy036 x)),
        ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
        ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb075AlphaDummy035))
          (Class.cab (nb075AlphaDummy005)
            (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
              (Wff.classEq (Class.cv (nb075AlphaDummy005))
                (synCun (synCphi (Class.cv (nb075AlphaDummy006))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb075AlphaDummy035))
            (Class.cab (nb075AlphaDummy005)
              (synWrex (nb075AlphaDummy006) (Class.cv (nb075AlphaDummy001))
                (Wff.classEq (Class.cv (nb075AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy006)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb075AlphaDummy036 x))
          (Class.cab (nb075AlphaDummy007 x)
            (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb075AlphaDummy036 x))
            (Class.cab (nb075AlphaDummy007 x)
              (synWrex (nb075AlphaDummy008 x) (Class.cv (nb075AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb075AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb075AlphaDummy008 x)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy006) from
                    (by
                      unfold nb075AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 1))))
                  (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy008 x) from (by
                      unfold nb075AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0036 x) 1))))
                  (TAlphaVar.there (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy005) from
                      (by
                        unfold nb075AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0034) 0))))
                    (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy007 x) from (by
                        unfold nb075AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb075_support_mem_0036 x) 0)))) (TAlphaVar.there
                      (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy035) from (by
                          unfold nb075AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0038) 0))))
                      (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy036 x) from (by
                          unfold nb075AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0039 x) 0))))
                      (TAlphaVar.there
                        (show (nb075AlphaDummy001) ≠ (nb075AlphaDummy009) from (by
                            unfold nb075AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb075_support_mem_0035) 0))))
                        (show (nb075AlphaDummy002 x) ≠ (nb075AlphaDummy010 x) from (by
                            unfold nb075AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb075_support_mem_0037 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb075AlphaDummy000))).fv ∪
                      ((Class.cv (nb075AlphaDummy001))).fv) (by decide)) (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb075AlphaDummy002 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy039) from (by
          unfold nb075AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0042) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy040 x) from (by
          unfold nb075AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy037) from (by
          unfold nb075AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0040) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy038 x) from (by
          unfold nb075AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy013) ≠ (nb075AlphaDummy017) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy039) from (by
          unfold nb075AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0042) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy040 x) from (by
          unfold nb075AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb075AlphaDummy006) ≠ (nb075AlphaDummy037) from (by
          unfold nb075AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0040) 0)))) (show (nb075AlphaDummy008 x) ≠
        (nb075AlphaDummy038 x) from (by
          unfold nb075AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy020) ≠ (nb075AlphaDummy027) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075AlphaDummy020) ≠
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075AlphaDummy013) ≠ (nb075AlphaDummy017) from (by
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
        ((nb075AlphaDummy039), (nb075AlphaDummy040 x)), ((nb075AlphaDummy037),
        (nb075AlphaDummy038 x)), ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
        ((nb075AlphaDummy005), (nb075AlphaDummy007 x)), ((nb075AlphaDummy035),
        (nb075AlphaDummy036 x)), ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
        ((nb075AlphaDummy001), (nb075AlphaDummy002 x)), ((nb075AlphaDummy000), x),
        ((nb075AlphaDummy003), (nb075AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb075AlphaDummy037), (nb075AlphaDummy038 x)),
                          ((nb075AlphaDummy006), (nb075AlphaDummy008 x)),
                          ((nb075AlphaDummy005), (nb075AlphaDummy007 x)),
                          ((nb075AlphaDummy035), (nb075AlphaDummy036 x)),
                          ((nb075AlphaDummy009), (nb075AlphaDummy010 x)),
                          ((nb075AlphaDummy001), (nb075AlphaDummy002 x)),
                          ((nb075AlphaDummy000), x),
                          ((nb075AlphaDummy003), (nb075AlphaDummy004 x))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb075SplitAlpha0000 x))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
