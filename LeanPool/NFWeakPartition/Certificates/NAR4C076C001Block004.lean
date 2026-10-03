/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C076C001Part010`. -/


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
noncomputable def nb076_split_alpha_0004 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) :
    TAlphaWff
      [((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)),
        ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
        ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_087))
          (Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_087)) (Class.cab (nb076_alpha_dummy_081)
              (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_088 g a b))
          (Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_088 g a b))
            (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_082) from
                    (by
                      unfold nb076_alpha_dummy_082;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
                  (show a ≠ (nb076_alpha_dummy_084 g a b) from (by
                      unfold nb076_alpha_dummy_084;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
                  (TAlphaVar.there (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_081) from
                      (by
                        unfold nb076_alpha_dummy_081;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))))
                    (show a ≠ (nb076_alpha_dummy_083 g a b) from (by
                        unfold nb076_alpha_dummy_083;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_087) from (by
                          unfold nb076_alpha_dummy_087;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0096) 0))))
                      (show a ≠ (nb076_alpha_dummy_088 g a b) from (by
                          unfold nb076_alpha_dummy_088;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0097 g a b) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_085) from (by
                            unfold nb076_alpha_dummy_085;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0093) 0))))
                        (show a ≠ (nb076_alpha_dummy_086 g a b) from (by
                            unfold nb076_alpha_dummy_086;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0095 g a b) 0))))
                        (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_g
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_000))).fv ∪
                      ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
                          (Class.cv (nb076_alpha_dummy_002)))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_089) from (by
                              unfold nb076_alpha_dummy_089;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                            (nb076_alpha_dummy_084 g a b) ≠ (nb076_alpha_dummy_091 g a b) from
                            (by
                              unfold nb076_alpha_dummy_091;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0099 g a b) 0))))
                          (TAlphaVar.there
                            (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_090) from (by
                                unfold nb076_alpha_dummy_090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0098) 1)))) (show
                              (nb076_alpha_dummy_084 g a b) ≠ (nb076_alpha_dummy_092 g a b) from
                              (by
                                unfold nb076_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076_alpha_dummy_082))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_096) from (by
          unfold nb076_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 1)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_099 g a b) from (by
          unfold nb076_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_095)
        from (by
          unfold nb076_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 0)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_098 g a b) from (by
          unfold nb076_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093)
        from (by
          unfold nb076_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100) 0)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_094 g a b) from (by
          unfold nb076_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087),
        (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠
        (nb076_alpha_dummy_103) from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_103)
        from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g a b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_103) from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_103)
        from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087),
        (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a
        b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_107) from (by
          unfold
            nb076_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_108 g a b) from
        (by
          unfold
            nb076_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_107)
        from (by
          unfold
            nb076_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_108 g a b) from
        (by
          unfold
            nb076_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_109) from (by
          unfold
            nb076_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_110 g a b) from
        (by
          unfold
            nb076_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g a b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠
        (nb076_alpha_dummy_109) from (by
          unfold
            nb076_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_110 g a b) from
        (by
          unfold
            nb076_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
                                        unfold nb076_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0100)
                                                0)))) (show (nb076_alpha_dummy_091 g a b) ≠
                                        (nb076_alpha_dummy_094 g a b) from (by
                                        unfold nb076_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0101 g a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)),
                                    ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)),
                                    ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)),
                                    ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                    ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                    ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)),
                                    ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                    ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                                    ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from
                                    (by
                                      unfold nb076_alpha_dummy_093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0100)
                                              0)))) (show (nb076_alpha_dummy_091 g a b) ≠
                                      (nb076_alpha_dummy_094 g a b) from (by
                                      unfold nb076_alpha_dummy_094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0101 g a b) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
                                        unfold nb076_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0100)
                                                0)))) (show (nb076_alpha_dummy_091 g a b) ≠
                                        (nb076_alpha_dummy_094 g a b) from (by
                                        unfold nb076_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0101 g a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)),
                                    ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)),
                                    ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)),
                                    ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                    ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                    ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)),
                                    ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                    ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                                    ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_082) from
                      (by
                        unfold nb076_alpha_dummy_082;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
                    (show a ≠ (nb076_alpha_dummy_084 g a b) from (by
                        unfold nb076_alpha_dummy_084;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_081) from (by
                          unfold nb076_alpha_dummy_081;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0092) 0))))
                      (show a ≠ (nb076_alpha_dummy_083 g a b) from (by
                          unfold nb076_alpha_dummy_083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_087) from (by
                            unfold nb076_alpha_dummy_087;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0096) 0))))
                        (show a ≠ (nb076_alpha_dummy_088 g a b) from (by
                            unfold nb076_alpha_dummy_088;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0097 g a b) 0))))
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_085) from (by
                              unfold nb076_alpha_dummy_085;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0093) 0))))
                          (show a ≠ (nb076_alpha_dummy_086 g a b) from (by
                              unfold nb076_alpha_dummy_086;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0095 g a b) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_g
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb076_alpha_dummy_000))).fv ∪
                        ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
                            (Class.cv (nb076_alpha_dummy_002)))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_089) from (by
                                unfold nb076_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                              (nb076_alpha_dummy_084 g a b) ≠ (nb076_alpha_dummy_091 g a b) from
                              (by
                                unfold nb076_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                        0)))) (TAlphaVar.there
                              (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_090) from (by
                                  unfold nb076_alpha_dummy_090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0098) 1)))) (show
                                (nb076_alpha_dummy_084 g a b) ≠ (nb076_alpha_dummy_092 g a b)
                                from (by
                                  unfold nb076_alpha_dummy_092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076_alpha_dummy_082))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_096) from (by
          unfold nb076_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 1)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_099 g a b) from (by
          unfold nb076_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_095)
        from (by
          unfold nb076_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102) 0)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_098 g a b) from (by
          unfold nb076_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093)
        from (by
          unfold nb076_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0100)
                  0)))) (show (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_094 g a b) from
        (by
          unfold nb076_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0101 g a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087),
        (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠
        (nb076_alpha_dummy_103) from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_103)
        from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g a b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_103) from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0106)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0107
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0104)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0105
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_103)
        from (by
          unfold
            nb076_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0110)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_104 g a b) from
        (by
          unfold
            nb076_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0111
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_101)
        from (by
          unfold
            nb076_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0108)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_102 g a b) from
        (by
          unfold
            nb076_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0109
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087),
        (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a
        b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_107) from (by
          unfold
            nb076_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_108 g a b) from
        (by
          unfold
            nb076_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_107)
        from (by
          unfold
            nb076_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0114)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_108 g a b) from
        (by
          unfold
            nb076_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0115
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0112)
                  0)))) (show (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0113
                    g a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_109) from (by
          unfold
            nb076_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_110 g a b) from
        (by
          unfold
            nb076_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g a b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠
        (nb076_alpha_dummy_109) from (by
          unfold
            nb076_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0118)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_110 g a b) from
        (by
          unfold
            nb076_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0119
                    g a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_097) ≠ (nb076_alpha_dummy_105)
        from (by
          unfold
            nb076_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0116)
                  0)))) (show (nb076_alpha_dummy_100 g a b) ≠ (nb076_alpha_dummy_106 g a b) from
        (by
          unfold
            nb076_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0117
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from
                                        (by
                                          unfold nb076_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0100)
                                                  0)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_094 g a b) from (by
                                          unfold nb076_alpha_dummy_094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0101 g a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)),
                                      ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)),
                                      ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)),
                                      ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                      ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                      ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)),
                                      ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                      ((nb076_alpha_dummy_002), g),
                                      ((nb076_alpha_dummy_001), b),
                                      ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
                                        unfold nb076_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0100)
                                                0)))) (show (nb076_alpha_dummy_091 g a b) ≠
                                        (nb076_alpha_dummy_094 g a b) from (by
                                        unfold nb076_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0101 g a b) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from
                                        (by
                                          unfold nb076_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0100)
                                                  0)))) (show (nb076_alpha_dummy_091 g a b) ≠
        (nb076_alpha_dummy_094 g a b) from (by
                                          unfold nb076_alpha_dummy_094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0101 g a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)),
                                      ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)),
                                      ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)),
                                      ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                      ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                      ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)),
                                      ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                      ((nb076_alpha_dummy_002), g),
                                      ((nb076_alpha_dummy_001), b),
                                      ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part011`. -/


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
noncomputable def nb076_split_alpha_0005 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
        ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
        ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
        ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
        ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
        ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_125))
          (Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_125)) (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_126 g b))
          (Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_126 g b))
            (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_120) from
                    (by
                      unfold nb076_alpha_dummy_120;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
                  (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
                      unfold nb076_alpha_dummy_122;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0126 g b) 1)))) (TAlphaVar.there
                    (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_119) from (by
                        unfold nb076_alpha_dummy_119;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))))
                    (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
                        unfold nb076_alpha_dummy_121;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_125) from (by
                          unfold nb076_alpha_dummy_125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0128) 0))))
                      (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_126 g b) from (by
                          unfold nb076_alpha_dummy_126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0129 g b) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_123) from (by
                            unfold nb076_alpha_dummy_123;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0125) 0))))
                        (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_124 g b) from (by
                            unfold nb076_alpha_dummy_124;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0127 g b) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_001))).fv ∪
                              ((Class.cv (nb076_alpha_dummy_002))).fv) (by decide))
                          (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb076_alpha_dummy_113))).fv ∪
                      ((Class.cv (nb076_alpha_dummy_114))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
                      ((Class.cv (nb076_alpha_dummy_116 g b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_127) from (by
                              unfold nb076_alpha_dummy_127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0130) 0))))
                          (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_129 g b) from
                            (by
                              unfold nb076_alpha_dummy_129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0131 g b) 0))))
                          (TAlphaVar.there
                            (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_128) from (by
                                unfold nb076_alpha_dummy_128;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0130) 1)))) (show
                              (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_130 g b) from (by
                                unfold nb076_alpha_dummy_130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0131 g b) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076_alpha_dummy_120))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_122 g b))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_134) from (by
          unfold nb076_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 1)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_137 g b) from (by
          unfold nb076_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_133) from (by
          unfold nb076_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_136 g b) from (by
          unfold nb076_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131)
        from (by
          unfold nb076_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132) 0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_132 g b) from (by
          unfold nb076_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134),
        (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)),
        ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127),
        (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119),
        (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114),
        (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠
        (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134),
        (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)),
        ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127),
        (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119),
        (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114),
        (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g
        b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_145) from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_145)
        from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠
        (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                        unfold nb076_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0132)
                                                0)))) (show (nb076_alpha_dummy_129 g b) ≠
                                        (nb076_alpha_dummy_132 g b) from (by
                                        unfold nb076_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0133 g b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                                    ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                                    ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                                    ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                                    ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                                    ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
                                    ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                                    ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                                    ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                                    ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                                    ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                    ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                    ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                                    ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                    ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                                    ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from
                                    (by
                                      unfold nb076_alpha_dummy_131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0132)
                                              0)))) (show (nb076_alpha_dummy_129 g b) ≠
                                      (nb076_alpha_dummy_132 g b) from (by
                                      unfold nb076_alpha_dummy_132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0133 g b)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                        unfold nb076_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0132)
                                                0)))) (show (nb076_alpha_dummy_129 g b) ≠
                                        (nb076_alpha_dummy_132 g b) from (by
                                        unfold nb076_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0133 g b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                                    ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                                    ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                                    ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                                    ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                                    ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
                                    ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                                    ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                                    ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                                    ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                                    ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                    ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                    ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                                    ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                    ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                                    ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_120) from
                      (by
                        unfold nb076_alpha_dummy_120;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
                    (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
                        unfold nb076_alpha_dummy_122;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_119) from (by
                          unfold nb076_alpha_dummy_119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0124) 0))))
                      (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
                          unfold nb076_alpha_dummy_121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_125) from (by
                            unfold nb076_alpha_dummy_125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0128) 0))))
                        (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_126 g b) from (by
                            unfold nb076_alpha_dummy_126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0129 g b) 0))))
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_123) from (by
                              unfold nb076_alpha_dummy_123;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0125) 0))))
                          (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_124 g b) from
                            (by
                              unfold nb076_alpha_dummy_124;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0127 g b) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb076_alpha_dummy_001))).fv ∪
                                ((Class.cv (nb076_alpha_dummy_002))).fv) (by decide))
                            (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb076_alpha_dummy_113))).fv ∪
                        ((Class.cv (nb076_alpha_dummy_114))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
                        ((Class.cv (nb076_alpha_dummy_116 g b))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_127) from (by
                                unfold nb076_alpha_dummy_127;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0130) 0)))) (show
                              (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_129 g b) from (by
                                unfold nb076_alpha_dummy_129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0131 g b) 0))))
                            (TAlphaVar.there
                              (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_128) from (by
                                  unfold nb076_alpha_dummy_128;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0130) 1)))) (show
                                (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_130 g b) from
                                (by
                                  unfold nb076_alpha_dummy_130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0131 g b)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076_alpha_dummy_120))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076_alpha_dummy_122 g b))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_134) from (by
          unfold nb076_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 1)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_137 g b) from (by
          unfold nb076_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_133)
        from (by
          unfold nb076_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_136 g b) from (by
          unfold nb076_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131)
        from (by
          unfold nb076_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132)
                  0)))) (show (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from (by
          unfold nb076_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134),
        (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)),
        ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127),
        (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119),
        (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114),
        (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠
        (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134),
        (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)),
        ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127),
        (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119),
        (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114),
        (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g
        b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_145) from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_145)
        from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠
        (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from
                                        (by
                                          unfold nb076_alpha_dummy_131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0132)
                                                  0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_132 g b) from (by
                                          unfold nb076_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0133 g b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                                      ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                                      ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                                      ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                                      ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                                      ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
                                      ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                                      ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                                      ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                                      ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                                      ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                      ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                      ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                                      ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                      ((nb076_alpha_dummy_002), g),
                                      ((nb076_alpha_dummy_001), b),
                                      ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                        unfold nb076_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0132)
                                                0)))) (show (nb076_alpha_dummy_129 g b) ≠
                                        (nb076_alpha_dummy_132 g b) from (by
                                        unfold nb076_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0133 g b) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from
                                        (by
                                          unfold nb076_alpha_dummy_131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0132)
                                                  0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_132 g b) from (by
                                          unfold nb076_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0133 g b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                                      ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                                      ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                                      ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                                      ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                                      ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)),
                                      ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                                      ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                                      ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                                      ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                                      ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                                      ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                                      ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                                      ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                                      ((nb076_alpha_dummy_002), g),
                                      ((nb076_alpha_dummy_001), b),
                                      ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part012`. -/


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
noncomputable def nb076_split_alpha_0006 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
        ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
        ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
        ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
        ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
        ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
        ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
        ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_153))
          (syn_cphi (Class.cv (nb076_alpha_dummy_120)))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_153))
            (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_154 g b))
          (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_154 g b))
            (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_127) from
                    (by
                      unfold nb076_alpha_dummy_127;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0130) 0))))
                  (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_129 g b) from (by
                      unfold nb076_alpha_dummy_129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0131 g b) 0)))) (TAlphaVar.there
                    (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_128) from (by
                        unfold nb076_alpha_dummy_128;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0130) 1))))
                    (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_130 g b) from (by
                        unfold nb076_alpha_dummy_130;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0131 g b) 1))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_153) from (by
                          unfold nb076_alpha_dummy_153;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0160) 0))))
                      (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_154 g b) from (by
                          unfold nb076_alpha_dummy_154;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0161 g b) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_151) from (by
                            unfold nb076_alpha_dummy_151;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0158) 0))))
                        (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_152 g b) from (by
                            unfold nb076_alpha_dummy_152;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0159 g b) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_120))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb076_alpha_dummy_122 g b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_134) from (by
                                        unfold nb076_alpha_dummy_134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0134)
                                                1)))) (show (nb076_alpha_dummy_129 g b) ≠
                                        (nb076_alpha_dummy_137 g b) from (by
                                        unfold nb076_alpha_dummy_137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0135 g b) 1))))
                                    (TAlphaVar.there (show
                                        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_133) from
                                        (by
                                          unfold nb076_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0134)
                                                  0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_136 g b) from (by
                                          unfold nb076_alpha_dummy_136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0135 g b) 0))))
                                      (TAlphaVar.there (show (nb076_alpha_dummy_127) ≠
        (nb076_alpha_dummy_131) from (by
          unfold nb076_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132) 0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_132 g b) from (by
          unfold nb076_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_135),
        (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)),
                                        ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)),
                                        ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                                        ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                                        ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                                        ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
                                        ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
                                        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                                        ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                                        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
                                        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                                        ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                                        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                                        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                                        ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
                                        ((nb076_alpha_dummy_001), b),
                                        ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
                                        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)),
        ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133),
        (nb076_alpha_dummy_136 g b)), ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
        ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128),
        (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
        ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)), ((nb076_alpha_dummy_120),
        (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)), ((nb076_alpha_dummy_123),
        (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117),
        (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠
        (nb076_alpha_dummy_145) from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_145)
        from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠
        (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                unfold nb076_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                              (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from (by
                                unfold nb076_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                            ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                            ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                            ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
                            ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
                            ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                            ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                            ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
                            ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                            ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                            ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                            ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                            ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                            ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                            ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                            ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                            ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                            ((nb076_alpha_dummy_000), a),
                            ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
                            ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                            ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                              unfold nb076_alpha_dummy_131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0132) 0))))
                          (show (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from
                            (by
                              unfold nb076_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                unfold nb076_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                              (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from (by
                                unfold nb076_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                            ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                            ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                            ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
                            ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
                            ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                            ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                            ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
                            ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                            ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                            ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                            ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                            ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                            ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                            ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                            ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                            ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                            ((nb076_alpha_dummy_000), a),
                            ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
                            ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                            ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_127) from (by
                        unfold nb076_alpha_dummy_127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0130) 0))))
                    (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_129 g b) from (by
                        unfold nb076_alpha_dummy_129;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0131 g b) 0))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_128) from (by
                          unfold nb076_alpha_dummy_128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0130) 1))))
                      (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_130 g b) from (by
                          unfold nb076_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0131 g b) 1))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_153) from (by
                            unfold nb076_alpha_dummy_153;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0160) 0))))
                        (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_154 g b) from (by
                            unfold nb076_alpha_dummy_154;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0161 g b) 0))))
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_120) ≠ (nb076_alpha_dummy_151) from (by
                              unfold nb076_alpha_dummy_151;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0158) 0))))
                          (show (nb076_alpha_dummy_122 g b) ≠ (nb076_alpha_dummy_152 g b) from
                            (by
                              unfold nb076_alpha_dummy_152;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0159 g b) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_120))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb076_alpha_dummy_122 g b))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_134) from
                                        (by
                                          unfold nb076_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0134)
                                                  1)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_137 g b) from (by
                                          unfold nb076_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0135 g b) 1))))
                                      (TAlphaVar.there (show (nb076_alpha_dummy_127) ≠
        (nb076_alpha_dummy_133) from (by
          unfold nb076_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0134) 0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_136 g b) from (by
          unfold nb076_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0135 g b) 0)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
          unfold nb076_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0132) 0)))) (show (nb076_alpha_dummy_129 g b) ≠
        (nb076_alpha_dummy_132 g b) from (by
          unfold nb076_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0133 g b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_135),
        (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)),
        ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)), ((nb076_alpha_dummy_131),
        (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
        ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_153),
        (nb076_alpha_dummy_154 g b)), ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
        ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119),
        (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
        ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114),
        (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
        ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_141) from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0138)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0139
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0136)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0137
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_141)
        from (by
          unfold
            nb076_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0142)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_142 g b) from (by
          unfold
            nb076_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0143
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_139)
        from (by
          unfold
            nb076_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0140)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_140 g b) from (by
          unfold
            nb076_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0141
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134),
        (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)),
        ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127),
        (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
        ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)), ((nb076_alpha_dummy_151),
        (nb076_alpha_dummy_152 g b)), ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
        ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_149),
        (nb076_alpha_dummy_150 g b)), ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
        ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113),
        (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
        ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠
        (nb076_alpha_dummy_145) from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_145)
        from (by
          unfold
            nb076_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0146)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_146 g b) from (by
          unfold
            nb076_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0147
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0144)
                  0)))) (show (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0145
                    g b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠
        (nb076_alpha_dummy_147) from (by
          unfold
            nb076_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0150)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_148 g b) from (by
          unfold
            nb076_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0151
                    g b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_135) ≠ (nb076_alpha_dummy_143)
        from (by
          unfold
            nb076_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0148)
                  0)))) (show (nb076_alpha_dummy_138 g b) ≠ (nb076_alpha_dummy_144 g b) from (by
          unfold
            nb076_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0149
                    g b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                  unfold nb076_alpha_dummy_131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                                (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from
                                (by
                                  unfold nb076_alpha_dummy_132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0133 g b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                              ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                              ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                              ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
                              ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
                              ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                              ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                              ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
                              ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                              ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                              ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                              ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                              ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                              ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                              ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                              ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                              ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                              ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                (nb076_alpha_dummy_006 g m n a b)),
                              ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                              ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                unfold nb076_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                              (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from (by
                                unfold nb076_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0133 g b) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_131) from (by
                                  unfold nb076_alpha_dummy_131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0132) 0)))) (show
                                (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_132 g b) from
                                (by
                                  unfold nb076_alpha_dummy_132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0133 g b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)),
                              ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)),
                              ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)),
                              ((nb076_alpha_dummy_153), (nb076_alpha_dummy_154 g b)),
                              ((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)),
                              ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)),
                              ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
                              ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)),
                              ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)),
                              ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
                              ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)),
                              ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)),
                              ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                              ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                              ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                              ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                              ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                              ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
                                (nb076_alpha_dummy_006 g m n a b)),
                              ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                              ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
