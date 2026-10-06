/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C068C001Part013Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part013`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0000`. -/
@[expose]
noncomputable def nb068SplitAlpha0000 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy021), (nb068AlphaDummy024 x y)),
        ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
        ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)),
        ((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
        ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
        ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
        ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
        ((nb068AlphaDummy011), (nb068AlphaDummy012 x y)),
        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
        ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy019))
            (synCun (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy022 x y))
            (synCun (Class.cv (nb068AlphaDummy023 x y))
              (Class.cv (nb068AlphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy021), (nb068AlphaDummy024 x y)),
          ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
          ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)),
          ((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
          ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
          ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
          ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
          ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
          ((nb068AlphaDummy011), (nb068AlphaDummy012 x y)),
          ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
          ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy031) from (by
                                unfold nb068AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy032 x y) from (by
                                unfold nb068AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy031) from (by
                                unfold nb068AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy032 x y) from (by
                                unfold nb068AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy033) from (by
                                unfold nb068AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy034 x y) from (by
                                unfold nb068AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy033) from (by
                                unfold nb068AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy034 x y) from (by
                                unfold nb068AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part014`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0001`. -/
@[expose]
noncomputable def nb068SplitAlpha0001 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
        ((nb068AlphaDummy011), (nb068AlphaDummy012 x y)),
        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
        ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy006))
          (Class.cv (nb068AlphaDummy001))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy005))
            (synCphi (Class.cv (nb068AlphaDummy006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy008 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy007 x y))
            (synCphi (Class.cv (nb068AlphaDummy008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy006) from (by
              unfold nb068AlphaDummy006;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))))
          (show x ≠ (nb068AlphaDummy008 x y) from (by
              unfold nb068AlphaDummy008;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))))
          (TAlphaVar.there (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy005) from (by
                unfold nb068AlphaDummy005;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))))
            (show x ≠ (nb068AlphaDummy007 x y) from (by
                unfold nb068AlphaDummy007;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy011) from (by
                  unfold nb068AlphaDummy011;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0008) 0))))
              (show x ≠ (nb068AlphaDummy012 x y) from (by
                  unfold nb068AlphaDummy012;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0009 x y) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy009) from (by
                    unfold nb068AlphaDummy009;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0005) 0))))
                (show x ≠ (nb068AlphaDummy010 x y) from (by
                    unfold nb068AlphaDummy010;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0007 x y) 0))))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb068AlphaDummy001))).fv ∪
                ((Class.cv (nb068AlphaDummy002))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy013) from
                      (by
                        unfold nb068AlphaDummy013;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0))))
                    (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy015 x y) from (by
                        unfold nb068AlphaDummy015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0011 x y) 0))))
                    (TAlphaVar.there
                      (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy014) from (by
                          unfold nb068AlphaDummy014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0010) 1))))
                      (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy016 x y) from (by
                          unfold nb068AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0011 x y) 1))))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy013) ≠ (nb068AlphaDummy020) from
                                        (by
                                          unfold nb068AlphaDummy020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0014)
                                                  1)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy023 x y) from (by
                                          unfold nb068AlphaDummy023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0015 x y) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy013) ≠
        (nb068AlphaDummy019) from (by
          unfold nb068AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0014) 0)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy022 x y) from (by
          unfold nb068AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0015 x y) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
          unfold nb068AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0012) 0)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy018 x y) from (by
          unfold nb068AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0013 x y) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb068AlphaDummy021),
        (nb068AlphaDummy024 x y)), ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
        ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)), ((nb068AlphaDummy017),
        (nb068AlphaDummy018 x y)), ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
        ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)), ((nb068AlphaDummy006),
        (nb068AlphaDummy008 x y)), ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
        ((nb068AlphaDummy011), (nb068AlphaDummy012 x y)), ((nb068AlphaDummy009),
        (nb068AlphaDummy010 x y)), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x), ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb068SplitAlpha0000 x y f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                  unfold nb068AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from
                                (by
                                  unfold nb068AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                              ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                              ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                              ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                              ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                              ((nb068AlphaDummy011), (nb068AlphaDummy012 x y)),
                              ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                              ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                unfold nb068AlphaDummy017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from (by
                                unfold nb068AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                  unfold nb068AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from
                                (by
                                  unfold nb068AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                              ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                              ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                              ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                              ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                              ((nb068AlphaDummy011), (nb068AlphaDummy012 x y)),
                              ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                              ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0002`. -/
@[expose]
noncomputable def nb068SplitAlpha0002 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy021), (nb068AlphaDummy024 x y)),
        ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
        ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)),
        ((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
        ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
        ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
        ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
        ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
        ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
        ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
        ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy019))
            (synCun (Class.cv (nb068AlphaDummy020)) (Class.cv (nb068AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy023 x y))
            (Class.cv (nb068AlphaDummy024 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy022 x y))
            (synCun (Class.cv (nb068AlphaDummy023 x y))
              (Class.cv (nb068AlphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy027) from (by
                              unfold nb068AlphaDummy027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy028 x y) from
                            (by
                              unfold nb068AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy025) from (by
                                unfold nb068AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy026 x y) from (by
                                unfold nb068AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy021), (nb068AlphaDummy024 x y)),
          ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
          ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)),
          ((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
          ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
          ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
          ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
          ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
          ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
          ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
          ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
          ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
          ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy031) from (by
                                unfold nb068AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy032 x y) from (by
                                unfold nb068AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy031) from (by
                                unfold nb068AlphaDummy031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy032 x y) from (by
                                unfold nb068AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy020) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068AlphaDummy023 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy033) from (by
                                unfold nb068AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy034 x y) from (by
                                unfold nb068AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy033) from (by
                                unfold nb068AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy034 x y) from (by
                                unfold nb068AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy021) ≠ (nb068AlphaDummy029) from (by
                                  unfold nb068AlphaDummy029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068AlphaDummy024 x y) ≠ (nb068AlphaDummy030 x y) from
                                (by
                                  unfold nb068AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0003`. -/
@[expose]
noncomputable def nb068SplitAlpha0003 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
        ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
        ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
        ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
        ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy039))
          (synCphi (Class.cv (nb068AlphaDummy006)))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy039))
            (synCphi (Class.cv (nb068AlphaDummy006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy040 x y))
          (synCphi (Class.cv (nb068AlphaDummy008 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy040 x y))
            (synCphi (Class.cv (nb068AlphaDummy008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy013) from
                    (by
                      unfold nb068AlphaDummy013;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0))))
                  (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy015 x y) from (by
                      unfold nb068AlphaDummy015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb068_support_mem_0011 x y) 0)))) (TAlphaVar.there
                    (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy014) from (by
                        unfold nb068AlphaDummy014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 1))))
                    (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy016 x y) from (by
                        unfold nb068AlphaDummy016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0011 x y) 1))))
                    (TAlphaVar.there
                      (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy039) from (by
                          unfold nb068AlphaDummy039;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0040) 0))))
                      (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy040 x y) from (by
                          unfold nb068AlphaDummy040;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0041 x y) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy037) from (by
                            unfold nb068AlphaDummy037;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0038) 0))))
                        (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy038 x y) from (by
                            unfold nb068AlphaDummy038;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0039 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy006))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb068AlphaDummy008 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy013) ≠ (nb068AlphaDummy020) from (by
                                        unfold nb068AlphaDummy020;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0014)
                                                1)))) (show (nb068AlphaDummy015 x y) ≠
                                        (nb068AlphaDummy023 x y) from (by
                                        unfold nb068AlphaDummy023;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb068_support_mem_0015 x y) 1))))
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy013) ≠ (nb068AlphaDummy019) from
                                        (by
                                          unfold nb068AlphaDummy019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0014)
                                                  0)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy022 x y) from (by
                                          unfold nb068AlphaDummy022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0015 x y) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy013) ≠
        (nb068AlphaDummy017) from (by
          unfold nb068AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0012) 0)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy018 x y) from (by
          unfold nb068AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0013 x y) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb068AlphaDummy021),
        (nb068AlphaDummy024 x y)), ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
                                        ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)),
                                        ((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                                        ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                                        ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                                        ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
                                        ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
                                        ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                                        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                                        ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                                        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                                        ((nb068AlphaDummy002), y),
                                        ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
        (nb068AlphaDummy004 x y f))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb068SplitAlpha0002 x y f))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                unfold nb068AlphaDummy017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from (by
                                unfold nb068AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                            ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                            ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                            ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
                            ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
                            ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                            ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                            ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                            ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                            ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                              unfold nb068AlphaDummy017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0012) 0))))
                          (show (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from
                            (by
                              unfold nb068AlphaDummy018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                unfold nb068AlphaDummy017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from (by
                                unfold nb068AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                            ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                            ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                            ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
                            ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
                            ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                            ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                            ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                            ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                            ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy013) from (by
                        unfold nb068AlphaDummy013;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0))))
                    (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy015 x y) from (by
                        unfold nb068AlphaDummy015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0011 x y) 0))))
                    (TAlphaVar.there
                      (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy014) from (by
                          unfold nb068AlphaDummy014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0010) 1))))
                      (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy016 x y) from (by
                          unfold nb068AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0011 x y) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy039) from (by
                            unfold nb068AlphaDummy039;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0040) 0))))
                        (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy040 x y) from (by
                            unfold nb068AlphaDummy040;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0041 x y) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy006) ≠ (nb068AlphaDummy037) from (by
                              unfold nb068AlphaDummy037;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0038) 0))))
                          (show (nb068AlphaDummy008 x y) ≠ (nb068AlphaDummy038 x y) from
                            (by
                              unfold nb068AlphaDummy038;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0039 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy013) ≠ (nb068AlphaDummy020) from
                                        (by
                                          unfold nb068AlphaDummy020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0014)
                                                  1)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy023 x y) from (by
                                          unfold nb068AlphaDummy023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0015 x y) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy013) ≠
        (nb068AlphaDummy019) from (by
          unfold nb068AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0014) 0)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy022 x y) from (by
          unfold nb068AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0015 x y) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
          unfold nb068AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0012) 0)))) (show (nb068AlphaDummy015 x y) ≠
        (nb068AlphaDummy018 x y) from (by
          unfold nb068AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0013 x y) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb068AlphaDummy021),
        (nb068AlphaDummy024 x y)), ((nb068AlphaDummy020), (nb068AlphaDummy023 x y)),
        ((nb068AlphaDummy019), (nb068AlphaDummy022 x y)), ((nb068AlphaDummy017),
        (nb068AlphaDummy018 x y)), ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
        ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)), ((nb068AlphaDummy039),
        (nb068AlphaDummy040 x y)), ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
        ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)), ((nb068AlphaDummy005),
        (nb068AlphaDummy007 x y)), ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x), ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb068SplitAlpha0002 x y f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                  unfold nb068AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from
                                (by
                                  unfold nb068AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                              ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                              ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                              ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
                              ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
                              ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                              ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                              ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                              ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                              ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                unfold nb068AlphaDummy017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from (by
                                unfold nb068AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy013) ≠ (nb068AlphaDummy017) from (by
                                  unfold nb068AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068AlphaDummy015 x y) ≠ (nb068AlphaDummy018 x y) from
                                (by
                                  unfold nb068AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy017), (nb068AlphaDummy018 x y)),
                              ((nb068AlphaDummy013), (nb068AlphaDummy015 x y)),
                              ((nb068AlphaDummy014), (nb068AlphaDummy016 x y)),
                              ((nb068AlphaDummy039), (nb068AlphaDummy040 x y)),
                              ((nb068AlphaDummy037), (nb068AlphaDummy038 x y)),
                              ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                              ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                              ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                              ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                              ((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0004`. -/
@[expose]
noncomputable def nb068SplitAlpha0004 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068AlphaDummy002), y), ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy003))
        (synCop (Class.cv (nb068AlphaDummy001)) (Class.cv (nb068AlphaDummy002))))
      (Wff.classEq (Class.cv (nb068AlphaDummy004 x y f))
        (synCop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy003) from (by
              unfold nb068AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0002) 0))))) (Ne.symm
          (show y ≠ (nb068AlphaDummy004 x y f) from (by
              unfold nb068AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0003 x y f) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb068AlphaDummy001) ≠ (nb068AlphaDummy003) from
              (by
                unfold nb068AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb068AlphaDummy004 x y f) from (by
                unfold nb068AlphaDummy004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0001 x y f) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0001 x y f dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0001 x y f dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy006) from (by
                                    unfold nb068AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0032) 1))))
                                (show y ≠ (nb068AlphaDummy008 x y) from (by
                                    unfold nb068AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy005) from
                                    (by
                                      unfold nb068AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0032)
                                              0)))) (show y ≠ (nb068AlphaDummy007 x y) from
                                    (by
                                      unfold nb068AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy002) ≠ (nb068AlphaDummy035) from (by
                                        unfold nb068AlphaDummy035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0036)
                                                0)))) (show y ≠ (nb068AlphaDummy036 x y) from
                                      (by
                                        unfold nb068AlphaDummy036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb068_support_mem_0037 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy002) ≠ (nb068AlphaDummy009) from
                                        (by
                                          unfold nb068AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0033)
                                                  0))))
                                      (show y ≠ (nb068AlphaDummy010 x y) from (by
                                          unfold nb068AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0035 x y) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy001))).fv ∪
                                    ((Class.cv (nb068AlphaDummy002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb068SplitAlpha0003 x y f)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb068AlphaDummy037),
        (nb068AlphaDummy038 x y)), ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                                        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                                        ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                                        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                                        ((nb068AlphaDummy002), y),
                                        ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
        (nb068AlphaDummy004 x y f))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy006) from (by
                                    unfold nb068AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0032) 1))))
                                (show y ≠ (nb068AlphaDummy008 x y) from (by
                                    unfold nb068AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy005) from
                                    (by
                                      unfold nb068AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0032)
                                              0)))) (show y ≠ (nb068AlphaDummy007 x y) from
                                    (by
                                      unfold nb068AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy002) ≠ (nb068AlphaDummy035) from (by
                                        unfold nb068AlphaDummy035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0036)
                                                0)))) (show y ≠ (nb068AlphaDummy036 x y) from
                                      (by
                                        unfold nb068AlphaDummy036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb068_support_mem_0037 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy002) ≠ (nb068AlphaDummy009) from
                                        (by
                                          unfold nb068AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0033)
                                                  0))))
                                      (show y ≠ (nb068AlphaDummy010 x y) from (by
                                          unfold nb068AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0035 x y) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy001))).fv ∪
                                    ((Class.cv (nb068AlphaDummy002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb068SplitAlpha0003 x y f)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb068AlphaDummy037),
        (nb068AlphaDummy038 x y)), ((nb068AlphaDummy006), (nb068AlphaDummy008 x y)),
                                        ((nb068AlphaDummy005), (nb068AlphaDummy007 x y)),
                                        ((nb068AlphaDummy035), (nb068AlphaDummy036 x y)),
                                        ((nb068AlphaDummy009), (nb068AlphaDummy010 x y)),
                                        ((nb068AlphaDummy002), y),
                                        ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
        (nb068AlphaDummy004 x y f))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
