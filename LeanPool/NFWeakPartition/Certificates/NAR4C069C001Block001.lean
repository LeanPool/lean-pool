/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C069C001Part002Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C069C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb069_split_alpha_0000`. -/
@[expose]
noncomputable def nb069SplitAlpha0000 (x : Var) (y : Var) (a : Var) (b : Var) :
    TAlphaWff
      [((nb069AlphaDummy022), (nb069AlphaDummy025 a b)),
        ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
        ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)),
        ((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
        ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
        ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
        ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
        ((nb069AlphaDummy012), (nb069AlphaDummy013 a b)),
        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
        ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
        ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb069AlphaDummy020))
            (synCun (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb069AlphaDummy023 a b))
            (synCun (Class.cv (nb069AlphaDummy024 a b))
              (Class.cv (nb069AlphaDummy025 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb069AlphaDummy022), (nb069AlphaDummy025 a b)),
          ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
          ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)),
          ((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
          ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
          ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
          ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
          ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
          ((nb069AlphaDummy012), (nb069AlphaDummy013 a b)),
          ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
          ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
          ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy032) from (by
                                unfold nb069AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy033 a b) from (by
                                unfold nb069AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy032) from (by
                                unfold nb069AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy033 a b) from (by
                                unfold nb069AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy034) from (by
                                unfold nb069AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy035 a b) from (by
                                unfold nb069AlphaDummy035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy034) from (by
                                unfold nb069AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy035 a b) from (by
                                unfold nb069AlphaDummy035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb069_split_alpha_0001`. -/
@[expose]
noncomputable def nb069SplitAlpha0001 (x : Var) (y : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) :
    TAlphaWff
      [((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
        ((nb069AlphaDummy012), (nb069AlphaDummy013 a b)),
        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
        ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
        ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb069AlphaDummy007))
          (Class.cv (nb069AlphaDummy000))) (Wff.neg
          (Wff.classEq (Class.cv (nb069AlphaDummy006))
            (synCphi (Class.cv (nb069AlphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb069AlphaDummy009 a b)) (Class.cv a)) (Wff.neg
          (Wff.classEq (Class.cv (nb069AlphaDummy008 a b))
            (synCphi (Class.cv (nb069AlphaDummy009 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy007) from (by
              unfold nb069AlphaDummy007;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1))))
          (show a ≠ (nb069AlphaDummy009 a b) from (by
              unfold nb069AlphaDummy009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1))))
          (TAlphaVar.there (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy006) from (by
                unfold nb069AlphaDummy006;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0))))
            (show a ≠ (nb069AlphaDummy008 a b) from (by
                unfold nb069AlphaDummy008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0))))
            (TAlphaVar.there (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy012) from (by
                  unfold nb069AlphaDummy012;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0008) 0))))
              (show a ≠ (nb069AlphaDummy013 a b) from (by
                  unfold nb069AlphaDummy013;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0009 a b) 0))))
              (TAlphaVar.there (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy010) from (by
                    unfold nb069AlphaDummy010;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0005) 0))))
                (show a ≠ (nb069AlphaDummy011 a b) from (by
                    unfold nb069AlphaDummy011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0007 a b) 0))))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_a_b (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb069AlphaDummy000))).fv ∪
                ((Class.cv (nb069AlphaDummy001))).fv) (by decide))
            (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy014) from
                      (by
                        unfold nb069AlphaDummy014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0))))
                    (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy016 a b) from (by
                        unfold nb069AlphaDummy016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb069_support_mem_0011 a b) 0))))
                    (TAlphaVar.there
                      (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy015) from (by
                          unfold nb069AlphaDummy015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0010) 1))))
                      (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy017 a b) from (by
                          unfold nb069AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0011 a b) 1))))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb069AlphaDummy007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb069AlphaDummy009 a b))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb069AlphaDummy014) ≠ (nb069AlphaDummy021) from
                                        (by
                                          unfold nb069AlphaDummy021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0014)
                                                  1)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy024 a b) from (by
                                          unfold nb069AlphaDummy024;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0015 a b) 1))))
                                      (TAlphaVar.there (show (nb069AlphaDummy014) ≠
        (nb069AlphaDummy020) from (by
          unfold nb069AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0014) 0)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy023 a b) from (by
          unfold nb069AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0015 a b) 0)))) (TAlphaVar.there (show
        (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
          unfold nb069AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0012) 0)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy019 a b) from (by
          unfold nb069AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0013 a b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb069AlphaDummy022),
        (nb069AlphaDummy025 a b)), ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
        ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)), ((nb069AlphaDummy018),
        (nb069AlphaDummy019 a b)), ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
        ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)), ((nb069AlphaDummy007),
        (nb069AlphaDummy009 a b)), ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
        ((nb069AlphaDummy012), (nb069AlphaDummy013 a b)), ((nb069AlphaDummy010),
        (nb069AlphaDummy011 a b)), ((nb069AlphaDummy001), b),
        ((nb069AlphaDummy000), a), ((nb069AlphaDummy004),
        (nb069AlphaDummy005 x y a b))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb069SplitAlpha0000 x y a b))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                  unfold nb069AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from
                                (by
                                  unfold nb069AlphaDummy019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                              ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                              ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                              ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                              ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                              ((nb069AlphaDummy012), (nb069AlphaDummy013 a b)),
                              ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                              ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
                              ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                unfold nb069AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from (by
                                unfold nb069AlphaDummy019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                  unfold nb069AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from
                                (by
                                  unfold nb069AlphaDummy019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                              ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                              ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                              ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                              ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                              ((nb069AlphaDummy012), (nb069AlphaDummy013 a b)),
                              ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                              ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
                              ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb069_split_alpha_0002`. -/
@[expose]
noncomputable def nb069SplitAlpha0002 (x : Var) (y : Var) (a : Var) (b : Var) :
    TAlphaWff
      [((nb069AlphaDummy022), (nb069AlphaDummy025 a b)),
        ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
        ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)),
        ((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
        ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
        ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
        ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
        ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
        ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
        ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
        ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
        ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb069AlphaDummy020))
            (synCun (Class.cv (nb069AlphaDummy021)) (Class.cv (nb069AlphaDummy022))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb069AlphaDummy024 a b))
            (Class.cv (nb069AlphaDummy025 a b))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb069AlphaDummy023 a b))
            (synCun (Class.cv (nb069AlphaDummy024 a b))
              (Class.cv (nb069AlphaDummy025 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy028) from (by
                              unfold nb069AlphaDummy028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy029 a b) from
                            (by
                              unfold nb069AlphaDummy029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy026) from (by
                                unfold nb069AlphaDummy026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy027 a b) from (by
                                unfold nb069AlphaDummy027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb069AlphaDummy022), (nb069AlphaDummy025 a b)),
          ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
          ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)),
          ((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
          ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
          ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
          ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
          ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
          ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
          ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
          ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
          ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
          ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
          ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy032) from (by
                                unfold nb069AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy033 a b) from (by
                                unfold nb069AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy032) from (by
                                unfold nb069AlphaDummy032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy033 a b) from (by
                                unfold nb069AlphaDummy033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy021) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069AlphaDummy024 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy016 a b))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy034) from (by
                                unfold nb069AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy035 a b) from (by
                                unfold nb069AlphaDummy035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy034) from (by
                                unfold nb069AlphaDummy034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy035 a b) from (by
                                unfold nb069AlphaDummy035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069AlphaDummy022) ≠ (nb069AlphaDummy030) from (by
                                  unfold nb069AlphaDummy030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069AlphaDummy025 a b) ≠ (nb069AlphaDummy031 a b) from
                                (by
                                  unfold nb069AlphaDummy031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C069C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb069_split_alpha_0003`. -/
@[expose]
noncomputable def nb069SplitAlpha0003 (x : Var) (y : Var) (a : Var) (b : Var) :
    TAlphaWff
      [((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
        ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
        ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
        ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
        ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
        ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb069AlphaDummy040))
          (synCphi (Class.cv (nb069AlphaDummy007)))) (Wff.neg
          (Wff.classMem (Class.cv (nb069AlphaDummy040))
            (synCphi (Class.cv (nb069AlphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb069AlphaDummy041 a b))
          (synCphi (Class.cv (nb069AlphaDummy009 a b)))) (Wff.neg
          (Wff.classMem (Class.cv (nb069AlphaDummy041 a b))
            (synCphi (Class.cv (nb069AlphaDummy009 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy014) from
                    (by
                      unfold nb069AlphaDummy014;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0))))
                  (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy016 a b) from (by
                      unfold nb069AlphaDummy016;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb069_support_mem_0011 a b) 0)))) (TAlphaVar.there
                    (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy015) from (by
                        unfold nb069AlphaDummy015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 1))))
                    (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy017 a b) from (by
                        unfold nb069AlphaDummy017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb069_support_mem_0011 a b) 1))))
                    (TAlphaVar.there
                      (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy040) from (by
                          unfold nb069AlphaDummy040;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0040) 0))))
                      (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy041 a b) from (by
                          unfold nb069AlphaDummy041;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0041 a b) 0))))
                      (TAlphaVar.there
                        (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy038) from (by
                            unfold nb069AlphaDummy038;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0038) 0))))
                        (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy039 a b) from (by
                            unfold nb069AlphaDummy039;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0039 a b) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb069AlphaDummy007))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb069AlphaDummy009 a b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb069AlphaDummy014) ≠ (nb069AlphaDummy021) from (by
                                        unfold nb069AlphaDummy021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb069_support_mem_0014)
                                                1)))) (show (nb069AlphaDummy016 a b) ≠
                                        (nb069AlphaDummy024 a b) from (by
                                        unfold nb069AlphaDummy024;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb069_support_mem_0015 a b) 1))))
                                    (TAlphaVar.there (show
                                        (nb069AlphaDummy014) ≠ (nb069AlphaDummy020) from
                                        (by
                                          unfold nb069AlphaDummy020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0014)
                                                  0)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy023 a b) from (by
                                          unfold nb069AlphaDummy023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0015 a b) 0))))
                                      (TAlphaVar.there (show (nb069AlphaDummy014) ≠
        (nb069AlphaDummy018) from (by
          unfold nb069AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0012) 0)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy019 a b) from (by
          unfold nb069AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0013 a b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb069AlphaDummy022),
        (nb069AlphaDummy025 a b)), ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
                                        ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)),
                                        ((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                                        ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                                        ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                                        ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
                                        ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
                                        ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                                        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                                        ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                                        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                                        ((nb069AlphaDummy001), b),
                                        ((nb069AlphaDummy000), a), ((nb069AlphaDummy004),
        (nb069AlphaDummy005 x y a b))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb069SplitAlpha0002 x y a b))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                unfold nb069AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from (by
                                unfold nb069AlphaDummy019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                            ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                            ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                            ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
                            ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
                            ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                            ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                            ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                            ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                            ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
                            ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                              unfold nb069AlphaDummy018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0012) 0))))
                          (show (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from
                            (by
                              unfold nb069AlphaDummy019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                unfold nb069AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from (by
                                unfold nb069AlphaDummy019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                            ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                            ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                            ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
                            ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
                            ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                            ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                            ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                            ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                            ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
                            ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy014) from (by
                        unfold nb069AlphaDummy014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0))))
                    (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy016 a b) from (by
                        unfold nb069AlphaDummy016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb069_support_mem_0011 a b) 0))))
                    (TAlphaVar.there
                      (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy015) from (by
                          unfold nb069AlphaDummy015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0010) 1))))
                      (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy017 a b) from (by
                          unfold nb069AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0011 a b) 1))))
                      (TAlphaVar.there
                        (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy040) from (by
                            unfold nb069AlphaDummy040;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0040) 0))))
                        (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy041 a b) from (by
                            unfold nb069AlphaDummy041;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0041 a b) 0))))
                        (TAlphaVar.there
                          (show (nb069AlphaDummy007) ≠ (nb069AlphaDummy038) from (by
                              unfold nb069AlphaDummy038;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0038) 0))))
                          (show (nb069AlphaDummy009 a b) ≠ (nb069AlphaDummy039 a b) from
                            (by
                              unfold nb069AlphaDummy039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0039 a b) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb069AlphaDummy007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb069AlphaDummy009 a b))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb069AlphaDummy014) ≠ (nb069AlphaDummy021) from
                                        (by
                                          unfold nb069AlphaDummy021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0014)
                                                  1)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy024 a b) from (by
                                          unfold nb069AlphaDummy024;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0015 a b) 1))))
                                      (TAlphaVar.there (show (nb069AlphaDummy014) ≠
        (nb069AlphaDummy020) from (by
          unfold nb069AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0014) 0)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy023 a b) from (by
          unfold nb069AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0015 a b) 0)))) (TAlphaVar.there (show
        (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
          unfold nb069AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0012) 0)))) (show (nb069AlphaDummy016 a b) ≠
        (nb069AlphaDummy019 a b) from (by
          unfold nb069AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0013 a b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb069AlphaDummy022),
        (nb069AlphaDummy025 a b)), ((nb069AlphaDummy021), (nb069AlphaDummy024 a b)),
        ((nb069AlphaDummy020), (nb069AlphaDummy023 a b)), ((nb069AlphaDummy018),
        (nb069AlphaDummy019 a b)), ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
        ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)), ((nb069AlphaDummy040),
        (nb069AlphaDummy041 a b)), ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
        ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)), ((nb069AlphaDummy006),
        (nb069AlphaDummy008 a b)), ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)), ((nb069AlphaDummy001), b),
        ((nb069AlphaDummy000), a), ((nb069AlphaDummy004),
        (nb069AlphaDummy005 x y a b))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb069SplitAlpha0002 x y a b))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                  unfold nb069AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from
                                (by
                                  unfold nb069AlphaDummy019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                              ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                              ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                              ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
                              ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
                              ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                              ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                              ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                              ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                              ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
                              ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                unfold nb069AlphaDummy018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from (by
                                unfold nb069AlphaDummy019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069AlphaDummy014) ≠ (nb069AlphaDummy018) from (by
                                  unfold nb069AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069AlphaDummy016 a b) ≠ (nb069AlphaDummy019 a b) from
                                (by
                                  unfold nb069AlphaDummy019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb069AlphaDummy018), (nb069AlphaDummy019 a b)),
                              ((nb069AlphaDummy014), (nb069AlphaDummy016 a b)),
                              ((nb069AlphaDummy015), (nb069AlphaDummy017 a b)),
                              ((nb069AlphaDummy040), (nb069AlphaDummy041 a b)),
                              ((nb069AlphaDummy038), (nb069AlphaDummy039 a b)),
                              ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                              ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                              ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                              ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                              ((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
                              ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb069_split_alpha_0004`. -/
@[expose]
noncomputable def nb069SplitAlpha0004 (x : Var) (y : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) :
    TAlphaWff
      [((nb069AlphaDummy001), b), ((nb069AlphaDummy000), a),
        ((nb069AlphaDummy004), (nb069AlphaDummy005 x y a b))]
      (Wff.classEq (Class.cv (nb069AlphaDummy004))
        (synCop (Class.cv (nb069AlphaDummy000)) (Class.cv (nb069AlphaDummy001))))
      (Wff.classEq (Class.cv (nb069AlphaDummy005 x y a b))
        (synCop (Class.cv a) (Class.cv b))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy004) from (by
              unfold nb069AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0002) 0))))) (Ne.symm
          (show b ≠ (nb069AlphaDummy005 x y a b) from (by
              unfold nb069AlphaDummy005;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0003 x y a b) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb069AlphaDummy000) ≠ (nb069AlphaDummy004) from
              (by
                unfold nb069AlphaDummy004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0000) 0))))) (Ne.symm
            (show a ≠ (nb069AlphaDummy005 x y a b) from (by
                unfold nb069AlphaDummy005;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0001 x y a b) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb069SplitAlpha0001 x y a b dv_a_b)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb069SplitAlpha0001 x y a b dv_a_b)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy007) from (by
                                    unfold nb069AlphaDummy007;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0032) 1))))
                                (show b ≠ (nb069AlphaDummy009 a b) from (by
                                    unfold nb069AlphaDummy009;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                            1)))) (TAlphaVar.there
                                  (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy006) from
                                    (by
                                      unfold nb069AlphaDummy006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0032)
                                              0)))) (show b ≠ (nb069AlphaDummy008 a b) from
                                    (by
                                      unfold nb069AlphaDummy008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                              0)))) (TAlphaVar.there (show
                                      (nb069AlphaDummy001) ≠ (nb069AlphaDummy036) from (by
                                        unfold nb069AlphaDummy036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb069_support_mem_0036)
                                                0)))) (show b ≠ (nb069AlphaDummy037 a b) from
                                      (by
                                        unfold nb069AlphaDummy037;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb069_support_mem_0037 a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb069AlphaDummy001) ≠ (nb069AlphaDummy010) from
                                        (by
                                          unfold nb069AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0033)
                                                  0))))
                                      (show b ≠ (nb069AlphaDummy011 a b) from (by
                                          unfold nb069AlphaDummy011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0035 a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy000))).fv ∪
                                    ((Class.cv (nb069AlphaDummy001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb069SplitAlpha0003 x y a b))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb069AlphaDummy038),
        (nb069AlphaDummy039 a b)), ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                                        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                                        ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                                        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                                        ((nb069AlphaDummy001), b),
                                        ((nb069AlphaDummy000), a), ((nb069AlphaDummy004),
        (nb069AlphaDummy005 x y a b))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy007) from (by
                                    unfold nb069AlphaDummy007;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0032) 1))))
                                (show b ≠ (nb069AlphaDummy009 a b) from (by
                                    unfold nb069AlphaDummy009;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                            1)))) (TAlphaVar.there
                                  (show (nb069AlphaDummy001) ≠ (nb069AlphaDummy006) from
                                    (by
                                      unfold nb069AlphaDummy006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0032)
                                              0)))) (show b ≠ (nb069AlphaDummy008 a b) from
                                    (by
                                      unfold nb069AlphaDummy008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                              0)))) (TAlphaVar.there (show
                                      (nb069AlphaDummy001) ≠ (nb069AlphaDummy036) from (by
                                        unfold nb069AlphaDummy036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb069_support_mem_0036)
                                                0)))) (show b ≠ (nb069AlphaDummy037 a b) from
                                      (by
                                        unfold nb069AlphaDummy037;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb069_support_mem_0037 a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb069AlphaDummy001) ≠ (nb069AlphaDummy010) from
                                        (by
                                          unfold nb069AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0033)
                                                  0))))
                                      (show b ≠ (nb069AlphaDummy011 a b) from (by
                                          unfold nb069AlphaDummy011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0035 a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069AlphaDummy000))).fv ∪
                                    ((Class.cv (nb069AlphaDummy001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb069SplitAlpha0003 x y a b))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb069AlphaDummy038),
        (nb069AlphaDummy039 a b)), ((nb069AlphaDummy007), (nb069AlphaDummy009 a b)),
                                        ((nb069AlphaDummy006), (nb069AlphaDummy008 a b)),
                                        ((nb069AlphaDummy036), (nb069AlphaDummy037 a b)),
                                        ((nb069AlphaDummy010), (nb069AlphaDummy011 a b)),
                                        ((nb069AlphaDummy001), b),
                                        ((nb069AlphaDummy000), a), ((nb069AlphaDummy004),
        (nb069AlphaDummy005 x y a b))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_lec`. -/
@[expose]
noncomputable def nominalDfLec (x : Var) (y : Var) (a : Var) (b : Var) (dv_a_b : a ≠ b)
    (dv_a_x : a ≠ x) (__dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synClec) (synCopab a b
          (synWrex x (.cv a) (synWrex y (.cv b) (synWss (.cv x) (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb069SplitAlpha0004 x y a b dv_a_b) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b
                          (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_x
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069AlphaDummy002) ≠ (nb069AlphaDummy044) from (by
          unfold nb069AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0044) 0)))) (show x ≠ (nb069AlphaDummy045 x y) from (by
          unfold nb069AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0045 x y) 0)))) (TAlphaVar.there (show
        (nb069AlphaDummy002) ≠ (nb069AlphaDummy042) from (by
          unfold nb069AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0042) 0)))) (show x ≠ (nb069AlphaDummy043 x y) from (by
          unfold nb069AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0043 x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069AlphaDummy003) ≠ (nb069AlphaDummy044) from (by
          unfold nb069AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0048) 0)))) (show y ≠ (nb069AlphaDummy045 x y) from (by
          unfold nb069AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0049 x y) 0)))) (TAlphaVar.there (show
        (nb069AlphaDummy003) ≠ (nb069AlphaDummy042) from (by
          unfold nb069AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0046) 0)))) (show y ≠ (nb069AlphaDummy043 x y) from (by
          unfold nb069AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0047 x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069AlphaDummy002) ≠ (nb069AlphaDummy044) from (by
          unfold nb069AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0044) 0)))) (show x ≠ (nb069AlphaDummy045 x y) from (by
          unfold nb069AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0045 x y) 0)))) (TAlphaVar.there (show
        (nb069AlphaDummy002) ≠ (nb069AlphaDummy042) from (by
          unfold nb069AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0042) 0)))) (show x ≠ (nb069AlphaDummy043 x y) from (by
          unfold nb069AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0043 x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069AlphaDummy003) ≠ (nb069AlphaDummy044) from (by
          unfold nb069AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0048) 0)))) (show y ≠ (nb069AlphaDummy045 x y) from (by
          unfold nb069AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0049 x y) 0)))) (TAlphaVar.there (show
        (nb069AlphaDummy003) ≠ (nb069AlphaDummy042) from (by
          unfold nb069AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0046) 0)))) (show y ≠ (nb069AlphaDummy043 x y) from (by
          unfold nb069AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0047 x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
