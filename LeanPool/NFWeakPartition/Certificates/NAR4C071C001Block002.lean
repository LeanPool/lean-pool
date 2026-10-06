/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C071C001Part003Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C071C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0000`. -/
@[expose]
noncomputable def nb071SplitAlpha0000 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy021), (nb071AlphaDummy024 x)),
        ((nb071AlphaDummy020), (nb071AlphaDummy023 x)),
        ((nb071AlphaDummy019), (nb071AlphaDummy022 x)),
        ((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
        ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
        ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
        ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
        ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
        ((nb071AlphaDummy011), (nb071AlphaDummy012 x)),
        ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb071AlphaDummy019))
            (synCun (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy022 x))
            (synCun (Class.cv (nb071AlphaDummy023 x))
              (Class.cv (nb071AlphaDummy024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb071AlphaDummy021), (nb071AlphaDummy024 x)),
          ((nb071AlphaDummy020), (nb071AlphaDummy023 x)),
          ((nb071AlphaDummy019), (nb071AlphaDummy022 x)),
          ((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
          ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
          ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
          ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
          ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
          ((nb071AlphaDummy011), (nb071AlphaDummy012 x)),
          ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)), ((nb071AlphaDummy000), x),
          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy031) from (by
                                unfold nb071AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy032 x) from (by
                                unfold nb071AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy031) from (by
                                unfold nb071AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy032 x) from (by
                                unfold nb071AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy033) from (by
                                unfold nb071AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy034 x) from (by
                                unfold nb071AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy033) from (by
                                unfold nb071AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy034 x) from (by
                                unfold nb071AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C071C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0001`. -/
@[expose]
noncomputable def nb071SplitAlpha0001 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
        ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
        ((nb071AlphaDummy011), (nb071AlphaDummy012 x)),
        ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy006))
          (Class.cv (nb071AlphaDummy000))) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy005))
            (synCphi (Class.cv (nb071AlphaDummy006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy008 x)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy007 x))
            (synCphi (Class.cv (nb071AlphaDummy008 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy006) from (by
              unfold nb071AlphaDummy006;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1))))
          (show x ≠ (nb071AlphaDummy008 x) from (by
              unfold nb071AlphaDummy008;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1))))
          (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy005) from (by
                unfold nb071AlphaDummy005;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0))))
            (show x ≠ (nb071AlphaDummy007 x) from (by
                unfold nb071AlphaDummy007;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0))))
            (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy011) from (by
                  unfold nb071AlphaDummy011;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0010) 0))))
              (show x ≠ (nb071AlphaDummy012 x) from (by
                  unfold nb071AlphaDummy012;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0011 x) 0))))
              (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy009) from (by
                    unfold nb071AlphaDummy009;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0007) 0))))
                (show x ≠ (nb071AlphaDummy010 x) from (by
                    unfold nb071AlphaDummy010;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0009 x) 0))))
                (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy001) from
                    (by
                      unfold nb071AlphaDummy001;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0004) 0))))
                  (show x ≠ (nb071AlphaDummy002 x) from (by
                      unfold nb071AlphaDummy002;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0005 x) 0))))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb071AlphaDummy000))).fv ∪
                ((Class.cv (nb071AlphaDummy001))).fv) (by decide)) (freshVar_injective
              (((Class.cv x)).fv ∪ ((Class.cv (nb071AlphaDummy002 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb071AlphaDummy006) ≠ (nb071AlphaDummy013) from
                      (by
                        unfold nb071AlphaDummy013;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 0))))
                    (show (nb071AlphaDummy008 x) ≠ (nb071AlphaDummy015 x) from (by
                        unfold nb071AlphaDummy015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0013 x) 0)))) (TAlphaVar.there
                      (show (nb071AlphaDummy006) ≠ (nb071AlphaDummy014) from (by
                          unfold nb071AlphaDummy014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0012) 1))))
                      (show (nb071AlphaDummy008 x) ≠ (nb071AlphaDummy016 x) from (by
                          unfold nb071AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0013 x) 1))))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb071AlphaDummy006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb071AlphaDummy008 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb071AlphaDummy013) ≠ (nb071AlphaDummy020) from
                                        (by
                                          unfold nb071AlphaDummy020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0016)
                                                  1)))) (show (nb071AlphaDummy015 x) ≠
        (nb071AlphaDummy023 x) from (by
                                          unfold nb071AlphaDummy023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0017 x) 1))))
                                      (TAlphaVar.there (show (nb071AlphaDummy013) ≠
        (nb071AlphaDummy019) from (by
          unfold nb071AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0016) 0)))) (show (nb071AlphaDummy015 x) ≠
        (nb071AlphaDummy022 x) from (by
          unfold nb071AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0017 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
          unfold nb071AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0014) 0)))) (show (nb071AlphaDummy015 x) ≠
        (nb071AlphaDummy018 x) from (by
          unfold nb071AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0015 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb071AlphaDummy021),
        (nb071AlphaDummy024 x)), ((nb071AlphaDummy020), (nb071AlphaDummy023 x)),
        ((nb071AlphaDummy019), (nb071AlphaDummy022 x)), ((nb071AlphaDummy017),
        (nb071AlphaDummy018 x)), ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
        ((nb071AlphaDummy014), (nb071AlphaDummy016 x)), ((nb071AlphaDummy006),
        (nb071AlphaDummy008 x)), ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
        ((nb071AlphaDummy011), (nb071AlphaDummy012 x)), ((nb071AlphaDummy009),
        (nb071AlphaDummy010 x)), ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x), ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb071SplitAlpha0000 x))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
                                  unfold nb071AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                              (show (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy018 x) from
                                (by
                                  unfold nb071AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
                              ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
                              ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
                              ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                              ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                              ((nb071AlphaDummy011), (nb071AlphaDummy012 x)),
                              ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                              ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                              ((nb071AlphaDummy000), x),
                              ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
                                unfold nb071AlphaDummy017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                            (show (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy018 x) from (by
                                unfold nb071AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
                                  unfold nb071AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                              (show (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy018 x) from
                                (by
                                  unfold nb071AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
                              ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
                              ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
                              ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                              ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                              ((nb071AlphaDummy011), (nb071AlphaDummy012 x)),
                              ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                              ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                              ((nb071AlphaDummy000), x),
                              ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0002`. -/
@[expose]
noncomputable def nb071SplitAlpha0002 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy021), (nb071AlphaDummy024 x)),
        ((nb071AlphaDummy020), (nb071AlphaDummy023 x)),
        ((nb071AlphaDummy019), (nb071AlphaDummy022 x)),
        ((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
        ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
        ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
        ((nb071AlphaDummy039), (nb071AlphaDummy040 x)),
        ((nb071AlphaDummy037), (nb071AlphaDummy038 x)),
        ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
        ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
        ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
        ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb071AlphaDummy019))
            (synCun (Class.cv (nb071AlphaDummy020)) (Class.cv (nb071AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb071AlphaDummy023 x))
            (Class.cv (nb071AlphaDummy024 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy022 x))
            (synCun (Class.cv (nb071AlphaDummy023 x))
              (Class.cv (nb071AlphaDummy024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy027) from (by
                              unfold nb071AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy028 x) from (by
                              unfold nb071AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy025) from (by
                                unfold nb071AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy026 x) from (by
                                unfold nb071AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb071AlphaDummy021), (nb071AlphaDummy024 x)),
          ((nb071AlphaDummy020), (nb071AlphaDummy023 x)),
          ((nb071AlphaDummy019), (nb071AlphaDummy022 x)),
          ((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
          ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
          ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
          ((nb071AlphaDummy039), (nb071AlphaDummy040 x)),
          ((nb071AlphaDummy037), (nb071AlphaDummy038 x)),
          ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
          ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
          ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
          ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)), ((nb071AlphaDummy000), x),
          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy031) from (by
                                unfold nb071AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy032 x) from (by
                                unfold nb071AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy031) from (by
                                unfold nb071AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy032 x) from (by
                                unfold nb071AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy020) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071AlphaDummy023 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy033) from (by
                                unfold nb071AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy034 x) from (by
                                unfold nb071AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy033) from (by
                                unfold nb071AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy034 x) from (by
                                unfold nb071AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy021) ≠ (nb071AlphaDummy029) from (by
                                  unfold nb071AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071AlphaDummy024 x) ≠ (nb071AlphaDummy030 x) from
                                (by
                                  unfold nb071AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0003`. -/
@[expose]
noncomputable def nb071SplitAlpha0003 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy039), (nb071AlphaDummy040 x)),
        ((nb071AlphaDummy037), (nb071AlphaDummy038 x)),
        ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
        ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
        ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
        ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.classMem (Class.cv (nb071AlphaDummy039))
        (synCphi (Class.cv (nb071AlphaDummy006))))
      (Wff.classMem (Class.cv (nb071AlphaDummy040 x))
        (synCphi (Class.cv (nb071AlphaDummy008 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv (TAlphaVar.there
                (show (nb071AlphaDummy006) ≠ (nb071AlphaDummy013) from (by
                    unfold nb071AlphaDummy013;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 0))))
                (show (nb071AlphaDummy008 x) ≠ (nb071AlphaDummy015 x) from (by
                    unfold nb071AlphaDummy015;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 0))))
                (TAlphaVar.there (show (nb071AlphaDummy006) ≠ (nb071AlphaDummy014) from
                    (by
                      unfold nb071AlphaDummy014;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 1))))
                  (show (nb071AlphaDummy008 x) ≠ (nb071AlphaDummy016 x) from (by
                      unfold nb071AlphaDummy016;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 1))))
                  (TAlphaVar.there (show (nb071AlphaDummy006) ≠ (nb071AlphaDummy039) from
                      (by
                        unfold nb071AlphaDummy039;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0042) 0))))
                    (show (nb071AlphaDummy008 x) ≠ (nb071AlphaDummy040 x) from (by
                        unfold nb071AlphaDummy040;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0043 x) 0)))) (TAlphaVar.there
                      (show (nb071AlphaDummy006) ≠ (nb071AlphaDummy037) from (by
                          unfold nb071AlphaDummy037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0040) 0))))
                      (show (nb071AlphaDummy008 x) ≠ (nb071AlphaDummy038 x) from (by
                          unfold nb071AlphaDummy038;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0041 x) 0))))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb071AlphaDummy006))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb071AlphaDummy008 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy020) from
                                    (by
                                      unfold nb071AlphaDummy020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0016)
                                              1)))) (show
                                    (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy023 x) from
                                    (by
                                      unfold nb071AlphaDummy023;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0017 x)
                                              1)))) (TAlphaVar.there (show
                                      (nb071AlphaDummy013) ≠ (nb071AlphaDummy019) from (by
                                        unfold nb071AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0016)
                                                0)))) (show (nb071AlphaDummy015 x) ≠
                                        (nb071AlphaDummy022 x) from (by
                                        unfold nb071AlphaDummy022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0017 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from
                                        (by
                                          unfold nb071AlphaDummy017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0014)
                                                  0)))) (show (nb071AlphaDummy015 x) ≠
        (nb071AlphaDummy018 x) from (by
                                          unfold nb071AlphaDummy018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0015 x) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb071AlphaDummy021), (nb071AlphaDummy024 x)),
                                      ((nb071AlphaDummy020), (nb071AlphaDummy023 x)),
                                      ((nb071AlphaDummy019), (nb071AlphaDummy022 x)),
                                      ((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
                                      ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
                                      ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
                                      ((nb071AlphaDummy039), (nb071AlphaDummy040 x)),
                                      ((nb071AlphaDummy037), (nb071AlphaDummy038 x)),
                                      ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                                      ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                                      ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
                                      ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                                      ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                                      ((nb071AlphaDummy000), x), ((nb071AlphaDummy003),
                                        (nb071AlphaDummy004 x))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb071SplitAlpha0002 x))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
                              unfold nb071AlphaDummy017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                          (show (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy018 x) from (by
                              unfold nb071AlphaDummy018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
                          ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
                          ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
                          ((nb071AlphaDummy039), (nb071AlphaDummy040 x)),
                          ((nb071AlphaDummy037), (nb071AlphaDummy038 x)),
                          ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                          ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                          ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
                          ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                          ((nb071AlphaDummy000), x),
                          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
                            unfold nb071AlphaDummy017;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                        (show (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy018 x) from (by
                            unfold nb071AlphaDummy018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb071AlphaDummy013) ≠ (nb071AlphaDummy017) from (by
                              unfold nb071AlphaDummy017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                          (show (nb071AlphaDummy015 x) ≠ (nb071AlphaDummy018 x) from (by
                              unfold nb071AlphaDummy018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb071AlphaDummy017), (nb071AlphaDummy018 x)),
                          ((nb071AlphaDummy013), (nb071AlphaDummy015 x)),
                          ((nb071AlphaDummy014), (nb071AlphaDummy016 x)),
                          ((nb071AlphaDummy039), (nb071AlphaDummy040 x)),
                          ((nb071AlphaDummy037), (nb071AlphaDummy038 x)),
                          ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                          ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                          ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
                          ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                          ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                          ((nb071AlphaDummy000), x),
                          ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0004`. -/
@[expose]
noncomputable def nb071SplitAlpha0004 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy001), (nb071AlphaDummy002 x)), ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.classEq (Class.cv (nb071AlphaDummy003))
        (synCop (Class.cv (nb071AlphaDummy000)) (Class.cv (nb071AlphaDummy001))))
      (Wff.classEq (Class.cv (nb071AlphaDummy004 x))
        (synCop (Class.cv x) (Class.cv (nb071AlphaDummy002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy003) from (by
              unfold nb071AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0002) 0))))) (Ne.symm
          (show (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy004 x) from (by
              unfold nb071AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0003 x) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy003) from
              (by
                unfold nb071AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb071AlphaDummy004 x) from (by
                unfold nb071AlphaDummy004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0001 x) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb071SplitAlpha0001 x)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb071SplitAlpha0001 x)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy006) from (by
                                    unfold nb071AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0034) 1)))) (show
                                  (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy008 x) from (by
                                    unfold nb071AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0036 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy005) from
                                    (by
                                      unfold nb071AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0034)
                                              0)))) (show
                                    (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy007 x) from
                                    (by
                                      unfold nb071AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0036 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb071AlphaDummy001) ≠ (nb071AlphaDummy035) from (by
                                        unfold nb071AlphaDummy035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0038)
                                                0)))) (show (nb071AlphaDummy002 x) ≠
                                        (nb071AlphaDummy036 x) from (by
                                        unfold nb071AlphaDummy036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0039 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb071AlphaDummy001) ≠ (nb071AlphaDummy009) from
                                        (by
                                          unfold nb071AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0035)
                                                  0)))) (show (nb071AlphaDummy002 x) ≠
        (nb071AlphaDummy010 x) from (by
                                          unfold nb071AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0037 x) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy000))).fv ∪
                                    ((Class.cv (nb071AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb071AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb071SplitAlpha0003 x)
        (nb071SplitAlpha0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb071AlphaDummy037),
        (nb071AlphaDummy038 x)), ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                                        ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                                        ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
                                        ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                                        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                                        ((nb071AlphaDummy000), x), ((nb071AlphaDummy003),
        (nb071AlphaDummy004 x))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy006) from (by
                                    unfold nb071AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0034) 1)))) (show
                                  (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy008 x) from (by
                                    unfold nb071AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0036 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb071AlphaDummy001) ≠ (nb071AlphaDummy005) from
                                    (by
                                      unfold nb071AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0034)
                                              0)))) (show
                                    (nb071AlphaDummy002 x) ≠ (nb071AlphaDummy007 x) from
                                    (by
                                      unfold nb071AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0036 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb071AlphaDummy001) ≠ (nb071AlphaDummy035) from (by
                                        unfold nb071AlphaDummy035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0038)
                                                0)))) (show (nb071AlphaDummy002 x) ≠
                                        (nb071AlphaDummy036 x) from (by
                                        unfold nb071AlphaDummy036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0039 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb071AlphaDummy001) ≠ (nb071AlphaDummy009) from
                                        (by
                                          unfold nb071AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0035)
                                                  0)))) (show (nb071AlphaDummy002 x) ≠
        (nb071AlphaDummy010 x) from (by
                                          unfold nb071AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0037 x) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071AlphaDummy000))).fv ∪
                                    ((Class.cv (nb071AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb071AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb071SplitAlpha0003 x)
        (nb071SplitAlpha0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb071AlphaDummy037),
        (nb071AlphaDummy038 x)), ((nb071AlphaDummy006), (nb071AlphaDummy008 x)),
                                        ((nb071AlphaDummy005), (nb071AlphaDummy007 x)),
                                        ((nb071AlphaDummy035), (nb071AlphaDummy036 x)),
                                        ((nb071AlphaDummy009), (nb071AlphaDummy010 x)),
                                        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                                        ((nb071AlphaDummy000), x), ((nb071AlphaDummy003),
        (nb071AlphaDummy004 x))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

theorem nb071_compact_fv_empty_0032 : (nb071AlphaDummy041) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0106 : (nb071AlphaDummy041) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy041, fv_syn_cncs] using (nb071_compact_fv_empty_0032)

theorem nb071_compact_fv_empty_0033 (x : Var) :
    (nb071AlphaDummy043 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0107 (x : Var) : (nb071AlphaDummy043 x) ∉ ((synCncs)).fv :=
  by simpa only [nb071AlphaDummy043, fv_syn_cncs] using (nb071_compact_fv_empty_0033 x)

theorem nb071_compact_fv_empty_0034 : (nb071AlphaDummy045) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0108 : (nb071AlphaDummy045) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy045, fv_syn_cncs] using (nb071_compact_fv_empty_0034)

theorem nb071_compact_fv_empty_0035 (x : Var) :
    (nb071AlphaDummy046 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0109 (x : Var) : (nb071AlphaDummy046 x) ∉ ((synCncs)).fv :=
  by simpa only [nb071AlphaDummy046, fv_syn_cncs] using (nb071_compact_fv_empty_0035 x)

theorem nb071_compact_fv_empty_0036 : (nb071AlphaDummy048) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0110 : (nb071AlphaDummy048) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy048, fv_syn_cncs] using (nb071_compact_fv_empty_0036)

theorem nb071_compact_fv_empty_0037 (x : Var) :
    (nb071AlphaDummy050 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0111 (x : Var) : (nb071AlphaDummy050 x) ∉ ((synCncs)).fv :=
  by simpa only [nb071AlphaDummy050, fv_syn_cncs] using (nb071_compact_fv_empty_0037 x)

theorem nb071_compact_fv_empty_0038 : (nb071AlphaDummy047) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0112 : (nb071AlphaDummy047) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy047, fv_syn_cncs] using (nb071_compact_fv_empty_0038)

theorem nb071_compact_fv_empty_0039 (x : Var) :
    (nb071AlphaDummy049 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0113 (x : Var) : (nb071AlphaDummy049 x) ∉ ((synCncs)).fv :=
  by simpa only [nb071AlphaDummy049, fv_syn_cncs] using (nb071_compact_fv_empty_0039 x)

theorem nb071_wpp_notmem_0114 : (nb071AlphaDummy001) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy001, fv_syn_cncs] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0115 (x : Var) : (nb071AlphaDummy002 x) ∉ ((synCncs)).fv :=
  by simpa only [nb071AlphaDummy002, fv_syn_cncs] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0116 : (nb071AlphaDummy000) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy000, fv_syn_cncs] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0117 (x : Var) : x ∉ ((synCncs)).fv := by
  simpa only [fv_syn_cncs] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0118 : (nb071AlphaDummy003) ∉ ((synCncs)).fv := by
  simpa only [nb071AlphaDummy003, fv_syn_cncs] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0119 (x : Var) : (nb071AlphaDummy004 x) ∉ ((synCncs)).fv :=
  by simpa only [nb071AlphaDummy004, fv_syn_cncs] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0008 (x : Var) :
    TEnvFresh
      [((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      ((synCncs)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb071AlphaDummy041) (nb071AlphaDummy043 x)
      (nb071_wpp_notmem_0106) (nb071_wpp_notmem_0107 x)
      (TEnvFresh.consFresh (nb071AlphaDummy045) (nb071AlphaDummy046 x)
        (nb071_wpp_notmem_0108) (nb071_wpp_notmem_0109 x)
        (TEnvFresh.consFresh (nb071AlphaDummy048) (nb071AlphaDummy050 x)
          (nb071_wpp_notmem_0110) (nb071_wpp_notmem_0111 x)
          (TEnvFresh.consFresh (nb071AlphaDummy047) (nb071AlphaDummy049 x)
            (nb071_wpp_notmem_0112) (nb071_wpp_notmem_0113 x)
            (TEnvFresh.consFresh (nb071AlphaDummy001) (nb071AlphaDummy002 x)
              (nb071_wpp_notmem_0114) (nb071_wpp_notmem_0115 x)
              (TEnvFresh.consFresh (nb071AlphaDummy000) x (nb071_wpp_notmem_0116)
                (nb071_wpp_notmem_0117 x)
                (TEnvFresh.consFresh (nb071AlphaDummy003) (nb071AlphaDummy004 x)
                  (nb071_wpp_notmem_0118) (nb071_wpp_notmem_0119 x)
                  (TEnvFresh.nil ((synCncs)).fv))))))))

/-- Checked nominal proof certificate identified upstream as `nb071_wpp_refl_0008`. -/
@[expose]
noncomputable def nb071WppRefl0008 (x : Var) :
    TReflOn
      [((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      ((synCncs)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0008 x)

theorem nb071_compact_fv_empty_0046 : (nb071AlphaDummy056) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0047 (x : Var) :
    (nb071AlphaDummy058 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0048 : (nb071AlphaDummy055) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0049 (x : Var) :
    (nb071AlphaDummy057 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0050 : (nb071AlphaDummy042) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0051 (x : Var) :
    (nb071AlphaDummy044 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
