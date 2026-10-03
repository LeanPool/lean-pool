/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C073C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C073C001Part008`. -/


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

@[expose]
noncomputable def nb073_split_alpha_0004 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
        ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
        ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_086))
          (Class.cab (nb073_alpha_dummy_080)
            (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_086)) (Class.cab (nb073_alpha_dummy_080)
              (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_080))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_087 x y))
          (Class.cab (nb073_alpha_dummy_082 x y)
            (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_087 x y))
            (Class.cab (nb073_alpha_dummy_082 x y)
              (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_081) from
                    (by
                      unfold nb073_alpha_dummy_081;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
                  (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
                      unfold nb073_alpha_dummy_083;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb073_support_mem_0098 x y) 1)))) (TAlphaVar.there
                    (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_080) from (by
                        unfold nb073_alpha_dummy_080;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))))
                    (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
                        unfold nb073_alpha_dummy_082;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
                    (TAlphaVar.there
                      (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_086) from (by
                          unfold nb073_alpha_dummy_086;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0100) 0))))
                      (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_087 x y) from (by
                          unfold nb073_alpha_dummy_087;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0101 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_084) from (by
                            unfold nb073_alpha_dummy_084;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0097) 0))))
                        (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_085 x y) from (by
                            unfold nb073_alpha_dummy_085;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0099 x y) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_000))).fv ∪
                              ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide))
                          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb073_alpha_dummy_014))).fv ∪
                      ((Class.cv (nb073_alpha_dummy_015))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
                      ((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_088) from (by
                              unfold nb073_alpha_dummy_088;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0102) 0))))
                          (show (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_090 x y) from
                            (by
                              unfold nb073_alpha_dummy_090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_089) from (by
                                unfold nb073_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                              (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_091 x y) from (by
                                unfold nb073_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073_alpha_dummy_081))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_083 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_095) from (by
          unfold nb073_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_098 x y) from (by
          unfold nb073_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y) 1)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_094) from (by
          unfold nb073_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_097 x y) from (by
          unfold nb073_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092)
        from (by
          unfold nb073_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_093 x y) from (by
          unfold nb073_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080),
        (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
        ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015),
        (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080),
        (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
        ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015),
        (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠
        (nb073_alpha_dummy_106) from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_106)
        from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠
        (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                    ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                    ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                    ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                    ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                    ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
                                    ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from
                                    (by
                                      unfold nb073_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0104)
                                              0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                      (nb073_alpha_dummy_093 x y) from (by
                                      unfold nb073_alpha_dummy_093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0105 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                    ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                    ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                    ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                    ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                    ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
                                    ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_081) from
                      (by
                        unfold nb073_alpha_dummy_081;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
                    (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
                        unfold nb073_alpha_dummy_083;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))))
                    (TAlphaVar.there
                      (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_080) from (by
                          unfold nb073_alpha_dummy_080;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0096) 0))))
                      (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
                          unfold nb073_alpha_dummy_082;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_086) from (by
                            unfold nb073_alpha_dummy_086;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0100) 0))))
                        (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_087 x y) from (by
                            unfold nb073_alpha_dummy_087;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0101 x y) 0))))
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_084) from (by
                              unfold nb073_alpha_dummy_084;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0097) 0))))
                          (show (nb073_alpha_dummy_016 x y) ≠ (nb073_alpha_dummy_085 x y) from
                            (by
                              unfold nb073_alpha_dummy_085;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0099 x y) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb073_alpha_dummy_000))).fv ∪
                                ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb073_alpha_dummy_014))).fv ∪
                        ((Class.cv (nb073_alpha_dummy_015))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪
                        ((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_088) from (by
                                unfold nb073_alpha_dummy_088;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 0)))) (show
                              (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_090 x y) from (by
                                unfold nb073_alpha_dummy_090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_089) from (by
                                  unfold nb073_alpha_dummy_089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                                (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_091 x y) from
                                (by
                                  unfold nb073_alpha_dummy_091;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0103 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb073_alpha_dummy_081))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb073_alpha_dummy_083 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_095) from (by
          unfold nb073_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_098 x y) from (by
          unfold nb073_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  1)))) (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_094)
        from (by
          unfold nb073_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_097 x y) from (by
          unfold nb073_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092)
        from (by
          unfold nb073_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104)
                  0)))) (show (nb073_alpha_dummy_090 x y) ≠ (nb073_alpha_dummy_093 x y) from (by
          unfold nb073_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080),
        (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
        ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015),
        (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)), ((nb073_alpha_dummy_080),
        (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
        ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)), ((nb073_alpha_dummy_015),
        (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠
        (nb073_alpha_dummy_106) from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_106)
        from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠
        (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from
                                        (by
                                          unfold nb073_alpha_dummy_092;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0104)
                                                  0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_093 x y) from (by
                                          unfold nb073_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0105 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                      ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                      ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                      ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                      ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                      ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
                                      ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                      ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                      ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                      ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                      ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                      ((nb073_alpha_dummy_001), y),
                                      ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
                                        (nb073_alpha_dummy_005 x y))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from
                                        (by
                                          unfold nb073_alpha_dummy_092;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0104)
                                                  0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_093 x y) from (by
                                          unfold nb073_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0105 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                      ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                      ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                      ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                      ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                      ((nb073_alpha_dummy_086), (nb073_alpha_dummy_087 x y)),
                                      ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                      ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                      ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                      ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                      ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                      ((nb073_alpha_dummy_001), y),
                                      ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
                                        (nb073_alpha_dummy_005 x y))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part009`. -/


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

@[expose]
noncomputable def nb073_split_alpha_0005 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073_alpha_dummy_112), (nb073_alpha_dummy_113 x y)),
        ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
        ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
        ((nb073_alpha_dummy_110), (nb073_alpha_dummy_111 x y)),
        ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
        ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_112))
          (syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_081))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_112)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_113 x y))
          (syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_113 x y))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_088) from (by
                              unfold nb073_alpha_dummy_088;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0102) 0))))
                          (show (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_090 x y) from
                            (by
                              unfold nb073_alpha_dummy_090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_089) from (by
                                unfold nb073_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                              (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_091 x y) from (by
                                unfold nb073_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_114) from (by
                                  unfold nb073_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0132) 0)))) (show
                                (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_115 x y) from
                                (by
                                  unfold nb073_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0133 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_112) from (by
                                    unfold nb073_alpha_dummy_112;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0130) 0)))) (show
                                  (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_113 x y) from
                                  (by
                                    unfold nb073_alpha_dummy_113;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0131 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073_alpha_dummy_081))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_083 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_095) from (by
          unfold nb073_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_098 x y) from (by
          unfold nb073_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y) 1)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_094) from (by
          unfold nb073_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_097 x y) from (by
          unfold nb073_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092)
        from (by
          unfold nb073_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_093 x y) from (by
          unfold nb073_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)), ((nb073_alpha_dummy_112),
        (nb073_alpha_dummy_113 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
        ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_110),
        (nb073_alpha_dummy_111 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)), ((nb073_alpha_dummy_112),
        (nb073_alpha_dummy_113 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
        ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_110),
        (nb073_alpha_dummy_111 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠
        (nb073_alpha_dummy_106) from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_106)
        from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠
        (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                    ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                    ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                    ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)),
                                    ((nb073_alpha_dummy_112), (nb073_alpha_dummy_113 x y)),
                                    ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                    ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                    ((nb073_alpha_dummy_110), (nb073_alpha_dummy_111 x y)),
                                    ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from
                                    (by
                                      unfold nb073_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0104)
                                              0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                      (nb073_alpha_dummy_093 x y) from (by
                                      unfold nb073_alpha_dummy_093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0105 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                    ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                    ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                    ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)),
                                    ((nb073_alpha_dummy_112), (nb073_alpha_dummy_113 x y)),
                                    ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                    ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                    ((nb073_alpha_dummy_110), (nb073_alpha_dummy_111 x y)),
                                    ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_088) from (by
                              unfold nb073_alpha_dummy_088;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0102) 0))))
                          (show (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_090 x y) from
                            (by
                              unfold nb073_alpha_dummy_090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_089) from (by
                                unfold nb073_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                              (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_091 x y) from (by
                                unfold nb073_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_114) from (by
                                  unfold nb073_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0132) 0)))) (show
                                (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_115 x y) from
                                (by
                                  unfold nb073_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0133 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073_alpha_dummy_081) ≠ (nb073_alpha_dummy_112) from (by
                                    unfold nb073_alpha_dummy_112;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0130) 0)))) (show
                                  (nb073_alpha_dummy_083 x y) ≠ (nb073_alpha_dummy_113 x y) from
                                  (by
                                    unfold nb073_alpha_dummy_113;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0131 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073_alpha_dummy_081))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_083 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_095) from (by
          unfold nb073_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_098 x y) from (by
          unfold nb073_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y) 1)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_094) from (by
          unfold nb073_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_097 x y) from (by
          unfold nb073_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092)
        from (by
          unfold nb073_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104) 0)))) (show (nb073_alpha_dummy_090 x y) ≠
        (nb073_alpha_dummy_093 x y) from (by
          unfold nb073_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)), ((nb073_alpha_dummy_112),
        (nb073_alpha_dummy_113 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
        ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_110),
        (nb073_alpha_dummy_111 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_102) from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_102)
        from (by
          unfold
            nb073_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_103 x y) from (by
          unfold
            nb073_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_100)
        from (by
          unfold
            nb073_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_101 x y) from (by
          unfold
            nb073_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_096), (nb073_alpha_dummy_099 x y)), ((nb073_alpha_dummy_095),
        (nb073_alpha_dummy_098 x y)), ((nb073_alpha_dummy_094), (nb073_alpha_dummy_097 x y)),
        ((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)), ((nb073_alpha_dummy_088),
        (nb073_alpha_dummy_090 x y)), ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
        ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)), ((nb073_alpha_dummy_112),
        (nb073_alpha_dummy_113 x y)), ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
        ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)), ((nb073_alpha_dummy_110),
        (nb073_alpha_dummy_111 x y)), ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_088))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_090 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠
        (nb073_alpha_dummy_106) from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_106)
        from (by
          unfold
            nb073_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_107 x y) from (by
          unfold
            nb073_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_095) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073_alpha_dummy_098 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠
        (nb073_alpha_dummy_108) from (by
          unfold
            nb073_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_109 x y) from (by
          unfold
            nb073_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_096) ≠ (nb073_alpha_dummy_104)
        from (by
          unfold
            nb073_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073_alpha_dummy_099 x y) ≠ (nb073_alpha_dummy_105 x y) from (by
          unfold
            nb073_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                    ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                    ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                    ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)),
                                    ((nb073_alpha_dummy_112), (nb073_alpha_dummy_113 x y)),
                                    ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                    ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                    ((nb073_alpha_dummy_110), (nb073_alpha_dummy_111 x y)),
                                    ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from
                                    (by
                                      unfold nb073_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0104)
                                              0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                      (nb073_alpha_dummy_093 x y) from (by
                                      unfold nb073_alpha_dummy_093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0105 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_088) ≠ (nb073_alpha_dummy_092) from (by
                                        unfold nb073_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073_alpha_dummy_090 x y) ≠
                                        (nb073_alpha_dummy_093 x y) from (by
                                        unfold nb073_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_092), (nb073_alpha_dummy_093 x y)),
                                    ((nb073_alpha_dummy_088), (nb073_alpha_dummy_090 x y)),
                                    ((nb073_alpha_dummy_089), (nb073_alpha_dummy_091 x y)),
                                    ((nb073_alpha_dummy_114), (nb073_alpha_dummy_115 x y)),
                                    ((nb073_alpha_dummy_112), (nb073_alpha_dummy_113 x y)),
                                    ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
                                    ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
                                    ((nb073_alpha_dummy_110), (nb073_alpha_dummy_111 x y)),
                                    ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb073_alpha_dummy_112), (nb073_alpha_dummy_113 x y)),
            ((nb073_alpha_dummy_081), (nb073_alpha_dummy_083 x y)),
            ((nb073_alpha_dummy_080), (nb073_alpha_dummy_082 x y)),
            ((nb073_alpha_dummy_110), (nb073_alpha_dummy_111 x y)),
            ((nb073_alpha_dummy_084), (nb073_alpha_dummy_085 x y)),
            ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
            ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
            ((nb073_alpha_dummy_078), (nb073_alpha_dummy_079 x y)),
            ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
            ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
            ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nominal_df_cross (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_ccross) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cxp (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb073_alpha_dummy_002) ≠ (nb073_alpha_dummy_004) from (by
                            unfold nb073_alpha_dummy_004;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0004) 0))))) (Ne.symm
                        (show (nb073_alpha_dummy_003 x y) ≠ (nb073_alpha_dummy_005 x y) from (by
                            unfold nb073_alpha_dummy_005;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0005 x y) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_004) from (by
                              unfold nb073_alpha_dummy_004;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0002) 0))))) (Ne.symm
                          (show y ≠ (nb073_alpha_dummy_005 x y) from (by
                              unfold nb073_alpha_dummy_005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0003 x y) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_004) from (by
                                unfold nb073_alpha_dummy_004;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0000) 0))))) (Ne.symm
                            (show x ≠ (nb073_alpha_dummy_005 x y) from (by
                                unfold nb073_alpha_dummy_005;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0001 x y) 0)))))
                          (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb073_split_alpha_0002 x y dv_x_y)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb073_split_alpha_0003 x y)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb073_split_alpha_0003 x y))))))))))))) (TAlphaWff.conj
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_002) from (by
                              unfold nb073_alpha_dummy_002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0006) 0))))
                          (show x ≠ (nb073_alpha_dummy_003 x y) from (by
                              unfold nb073_alpha_dummy_003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0007 x y) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.refl_of_closed
                        [((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                          ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                          ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_002) from (by
                              unfold nb073_alpha_dummy_002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0042) 0))))
                          (show y ≠ (nb073_alpha_dummy_003 x y) from (by
                              unfold nb073_alpha_dummy_003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0043 x y) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                          ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                          ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_078) from (by
                                        unfold nb073_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0094)
                                                0))))) (Ne.symm (show
                                      (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_079 x y)
                                      from (by
                                        unfold nb073_alpha_dummy_079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0095 x y) 0)))))
                                  (TAlphaVar.there (Ne.symm (show
                                        (nb073_alpha_dummy_014) ≠ (nb073_alpha_dummy_078) from
                                        (by
                                          unfold nb073_alpha_dummy_078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0092)
                                                  0))))) (Ne.symm (show
                                        (nb073_alpha_dummy_016 x y) ≠
        (nb073_alpha_dummy_079 x y) from (by
                                          unfold nb073_alpha_dummy_079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0093 x y) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg
        (TAlphaWff.neg (nb073_split_alpha_0004 x y))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_081) from (by
          unfold
            nb073_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  1)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
          unfold
            nb073_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  1)))) (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_080)
        from (by
          unfold
            nb073_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  0)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
          unfold
            nb073_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_110)
        from (by
          unfold
            nb073_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0128)
                  0)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_111 x y) from (by
          unfold
            nb073_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0129
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_084)
        from (by
          unfold
            nb073_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0125)
                  0)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_085 x y) from (by
          unfold
            nb073_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0127
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_014))).fv ∪
        ((Class.cv (nb073_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_017 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073_split_alpha_0005 x y))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_081) from (by
          unfold
            nb073_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  1)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_083 x y) from (by
          unfold
            nb073_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  1)))) (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_080)
        from (by
          unfold
            nb073_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  0)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_082 x y) from (by
          unfold
            nb073_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_110)
        from (by
          unfold
            nb073_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0128)
                  0)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_111 x y) from (by
          unfold
            nb073_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0129
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_084)
        from (by
          unfold
            nb073_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0125)
                  0)))) (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_085 x y) from (by
          unfold
            nb073_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0127
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_014))).fv ∪
        ((Class.cv (nb073_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_017 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073_split_alpha_0005 x y))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb073_alpha_dummy_000))).fv ∪
                                        ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cv (TAlphaVar.there
                                    (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_015) from
                                      (by
                                        unfold nb073_alpha_dummy_015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0014)
                                                1)))) (show x ≠ (nb073_alpha_dummy_017 x y) from
                                      (by
                                        unfold nb073_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0016 x y) 1))))
                                    (TAlphaVar.there (show
                                        (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_014) from
                                        (by
                                          unfold nb073_alpha_dummy_014;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0014)
                                                  0))))
                                      (show x ≠ (nb073_alpha_dummy_016 x y) from (by
                                          unfold nb073_alpha_dummy_016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0016 x y) 0))))
                                      (TAlphaVar.there (show (nb073_alpha_dummy_000) ≠
        (nb073_alpha_dummy_078) from (by
          unfold nb073_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0134) 0)))) (show x ≠ (nb073_alpha_dummy_079 x y) from (by
          unfold nb073_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0135 x y) 0)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_002) from (by
          unfold nb073_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0006) 0)))) (show x ≠ (nb073_alpha_dummy_003 x y) from (by
          unfold nb073_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_015) from (by
                                        unfold nb073_alpha_dummy_015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0050)
                                                1)))) (show y ≠ (nb073_alpha_dummy_017 x y) from
                                      (by
                                        unfold nb073_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0052 x y) 1))))
                                    (TAlphaVar.there (show
                                        (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_014) from
                                        (by
                                          unfold nb073_alpha_dummy_014;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0050)
                                                  0))))
                                      (show y ≠ (nb073_alpha_dummy_016 x y) from (by
                                          unfold nb073_alpha_dummy_016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0052 x y) 0))))
                                      (TAlphaVar.there (show (nb073_alpha_dummy_001) ≠
        (nb073_alpha_dummy_078) from (by
          unfold nb073_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0136) 0)))) (show y ≠ (nb073_alpha_dummy_079 x y) from (by
          unfold nb073_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0137 x y) 0)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_001) ≠ (nb073_alpha_dummy_002) from (by
          unfold nb073_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0042) 0)))) (show y ≠ (nb073_alpha_dummy_003 x y) from (by
          unfold nb073_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0043 x y) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
