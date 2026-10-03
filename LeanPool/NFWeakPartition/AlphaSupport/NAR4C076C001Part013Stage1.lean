/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block004

/-! NF weak partition development: NAR4C076C001Part013. -/


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

@[expose]
noncomputable def nb076_split_alpha_0007 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
        ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
        ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
        ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
        (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))
      (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
        (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb076_alpha_dummy_000))).fv ∪
            ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
                (Class.cv (nb076_alpha_dummy_002)))).fv) (by decide))
        (freshVar_injective (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv)
          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_089) from (by
                                    unfold nb076_alpha_dummy_089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                                  (nb076_alpha_dummy_084 g a b) ≠ (nb076_alpha_dummy_091 g a b)
                                  from (by
                                    unfold nb076_alpha_dummy_091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                            0)))) (TAlphaVar.there
                                  (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_090) from
                                    (by
                                      unfold nb076_alpha_dummy_090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0098)
                                              1)))) (show (nb076_alpha_dummy_084 g a b) ≠
                                      (nb076_alpha_dummy_092 g a b) from (by
                                      unfold nb076_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0099 g a b) 1))))
                                  (TAlphaVar.there (show
                                      (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_157) from (by
                                        unfold nb076_alpha_dummy_157;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0184)
                                                0)))) (show (nb076_alpha_dummy_084 g a b) ≠
                                        (nb076_alpha_dummy_158 g a b) from (by
                                        unfold nb076_alpha_dummy_158;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0185 g a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_155) from
                                        (by
                                          unfold nb076_alpha_dummy_155;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0182)
                                                  0)))) (show (nb076_alpha_dummy_084 g a b) ≠
        (nb076_alpha_dummy_156 g a b) from (by
                                          unfold nb076_alpha_dummy_156;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0183 g a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb076_alpha_dummy_082))).fv) (by decide))
                                (freshVar_injective
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
                  (nb076_support_mem_0102)
                  1)))) (show (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_099 g a b) from
        (by
          unfold nb076_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_095)
        from (by
          unfold nb076_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102)
                  0)))) (show (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_098 g a b) from
        (by
          unfold nb076_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g
                    a b)
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
                  (nb076_support_mem_0101
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a
        b))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a
        b))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a
        b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠
        (nb076_alpha_dummy_107) from (by
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
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
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠
        (nb076_alpha_dummy_093) from (by
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
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
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
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_089) from (by
                                    unfold nb076_alpha_dummy_089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0098) 0)))) (show
                                  (nb076_alpha_dummy_084 g a b) ≠ (nb076_alpha_dummy_091 g a b)
                                  from (by
                                    unfold nb076_alpha_dummy_091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0099 g a b)
                                            0)))) (TAlphaVar.there
                                  (show (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_090) from
                                    (by
                                      unfold nb076_alpha_dummy_090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0098)
                                              1)))) (show (nb076_alpha_dummy_084 g a b) ≠
                                      (nb076_alpha_dummy_092 g a b) from (by
                                      unfold nb076_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0099 g a b) 1))))
                                  (TAlphaVar.there (show
                                      (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_157) from (by
                                        unfold nb076_alpha_dummy_157;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0184)
                                                0)))) (show (nb076_alpha_dummy_084 g a b) ≠
                                        (nb076_alpha_dummy_158 g a b) from (by
                                        unfold nb076_alpha_dummy_158;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0185 g a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076_alpha_dummy_082) ≠ (nb076_alpha_dummy_155) from
                                        (by
                                          unfold nb076_alpha_dummy_155;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0182)
                                                  0)))) (show (nb076_alpha_dummy_084 g a b) ≠
        (nb076_alpha_dummy_156 g a b) from (by
                                          unfold nb076_alpha_dummy_156;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0183 g a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb076_alpha_dummy_082))).fv) (by decide))
                                (freshVar_injective
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
                  (nb076_support_mem_0102)
                  1)))) (show (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_099 g a b) from
        (by
          unfold nb076_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_095)
        from (by
          unfold nb076_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0102)
                  0)))) (show (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_098 g a b) from
        (by
          unfold nb076_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0103 g
                    a b)
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
                  (nb076_support_mem_0101
                    g a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a
        b))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096),
        (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095),
        (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a
        b))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a
        b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_096) ≠
        (nb076_alpha_dummy_107) from (by
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
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
                    g a
                    b)
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
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
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
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb076_alpha_dummy_089) ≠
        (nb076_alpha_dummy_093) from (by
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
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_093) from (by
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
                  (nb076_support_mem_0101 g a b) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_093),
        (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089),
        (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090),
        (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_157),
        (nb076_alpha_dummy_158 g a b)), ((nb076_alpha_dummy_155),
        (nb076_alpha_dummy_156 g a b)), ((nb076_alpha_dummy_082),
        (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081),
        (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085),
        (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g),
        ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_closed
              [((nb076_alpha_dummy_155), (nb076_alpha_dummy_156 g a b)),
                ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
                ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)),
                ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)),
                ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)),
                ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
                ((nb076_alpha_dummy_000), a),
                ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
                ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
              (syn_ccompl (syn_csn (syn_c0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))

theorem nb076_wpp_notmem_0418 : (nb076_alpha_dummy_002) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_002, fv_syn_cen] using (nb076_compact_fv_empty_0080)

theorem nb076_wpp_notmem_0419 (g : Var) : g ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0081 g)

theorem nb076_wpp_notmem_0420 : (nb076_alpha_dummy_001) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_001, fv_syn_cen] using (nb076_compact_fv_empty_0082)

theorem nb076_wpp_notmem_0421 (b : Var) : b ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0083 b)

theorem nb076_wpp_notmem_0422 : (nb076_alpha_dummy_000) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_000, fv_syn_cen] using (nb076_compact_fv_empty_0084)

theorem nb076_wpp_notmem_0423 (a : Var) : a ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0085 a)

theorem nb076_wpp_notmem_0424 : (nb076_alpha_dummy_005) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_005, fv_syn_cen] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0425 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_006, fv_syn_cen] using
    (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0426 : (nb076_alpha_dummy_004) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_004, fv_syn_cen] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0427 (n : Var) : n ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0428 : (nb076_alpha_dummy_003) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_003, fv_syn_cen] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0429 (m : Var) : m ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb076_compact_fv_empty_0033 m)

theorem nb076_wpp_notmem_0430 : (nb076_alpha_dummy_007) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_007, fv_syn_cen] using (nb076_compact_fv_empty_0034)

theorem nb076_wpp_notmem_0431 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_008 g m n a b) ∉ ((syn_cen)).fv := by
  simpa only [nb076_alpha_dummy_008, fv_syn_cen] using
    (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TEnvFresh
      [((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      ((syn_cen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0418)
      (nb076_wpp_notmem_0419 g)
      (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0420)
        (nb076_wpp_notmem_0421 b)
        (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0422)
          (nb076_wpp_notmem_0423 a)
          (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b)
            (nb076_wpp_notmem_0424) (nb076_wpp_notmem_0425 g m n a b)
            (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0426)
              (nb076_wpp_notmem_0427 n)
              (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0428)
                (nb076_wpp_notmem_0429 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007)
                  (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0430)
                  (nb076_wpp_notmem_0431 g m n a b) (TEnvFresh.nil ((syn_cen)).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
