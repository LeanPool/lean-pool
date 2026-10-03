/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C096M3Part003

/-! NF weak partition development: NAR4H5C096M3Part004. -/


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
noncomputable def nb096_split_alpha_0005 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_102 D R))
          (Class.cv (nb096_alpha_dummy_041 D R))) (Wff.neg
          (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
            (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_104 D R q))
          (Class.cv (nb096_alpha_dummy_043 D R q))) (Wff.neg
          (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
            (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_102 D R) from
            (by
              unfold nb096_alpha_dummy_102;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 1))))
          (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_104 D R q) from (by
              unfold nb096_alpha_dummy_104;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 1))))
          (TAlphaVar.there (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_101 D R) from
              (by
                unfold nb096_alpha_dummy_101;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 0))))
            (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_103 D R q) from (by
                unfold nb096_alpha_dummy_103;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 0))))
            (TAlphaVar.there
              (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_131 D R) from (by
                  unfold nb096_alpha_dummy_131;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0130 D R) 0))))
              (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_132 D R q) from (by
                  unfold nb096_alpha_dummy_132;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0131 D R q) 0))))
              (TAlphaVar.there
                (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_105 D R) from (by
                    unfold nb096_alpha_dummy_105;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0127 D R) 0))))
                (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_106 D R q) from (by
                    unfold nb096_alpha_dummy_106;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb096_support_mem_0129 D R q) 0)))) (TAlphaVar.there
                  (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                                  (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
                    (by decide)) (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
                ((Class.cv (nb096_alpha_dummy_041 D R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
                ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096_alpha_dummy_102 D R) ≠ (nb096_alpha_dummy_109 D R)
                                      from (by
                                        unfold nb096_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 0)))) (show
                                      (nb096_alpha_dummy_104 D R q) ≠
                                        (nb096_alpha_dummy_111 D R q) from (by
                                        unfold nb096_alpha_dummy_111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 0))))
                                    (TAlphaVar.there (show (nb096_alpha_dummy_102 D R) ≠
        (nb096_alpha_dummy_110 D R) from (by
                                          unfold nb096_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0104 D R) 1)))) (show
                                        (nb096_alpha_dummy_104 D R q) ≠
        (nb096_alpha_dummy_112 D R q) from (by
                                          unfold nb096_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0105 D R q) 1))))
                                      (TAlphaVar.there (show (nb096_alpha_dummy_102 D R) ≠
        (nb096_alpha_dummy_135 D R) from (by
          unfold nb096_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0134 D R) 0)))) (show (nb096_alpha_dummy_104 D R q) ≠
        (nb096_alpha_dummy_136 D R q) from (by
          unfold nb096_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0135 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_102 D R) ≠ (nb096_alpha_dummy_133 D R) from (by
          unfold nb096_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0132 D R) 0)))) (show (nb096_alpha_dummy_104 D R q) ≠
        (nb096_alpha_dummy_134 D R q) from (by
          unfold nb096_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0133 D R q) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb096_alpha_dummy_102 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb096_alpha_dummy_104 D R q))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_116 D R) from
        (by
          unfold nb096_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  1)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_119 D R q) from
        (by
          unfold nb096_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_115 D R) from (by
          unfold nb096_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_118 D R q) from
        (by
          unfold nb096_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold
            nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold
            nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_116
        D R) ≠ (nb096_alpha_dummy_127 D R) from (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_116
        D R) ≠ (nb096_alpha_dummy_127 D R) from (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠ (nb096_alpha_dummy_129 D R) from
        (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_129 D R) from (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_113 D R) from
        (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096_alpha_dummy_102 D R) ≠ (nb096_alpha_dummy_109 D R)
                                      from (by
                                        unfold nb096_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 0)))) (show
                                      (nb096_alpha_dummy_104 D R q) ≠
                                        (nb096_alpha_dummy_111 D R q) from (by
                                        unfold nb096_alpha_dummy_111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 0))))
                                    (TAlphaVar.there (show (nb096_alpha_dummy_102 D R) ≠
        (nb096_alpha_dummy_110 D R) from (by
                                          unfold nb096_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0104 D R) 1)))) (show
                                        (nb096_alpha_dummy_104 D R q) ≠
        (nb096_alpha_dummy_112 D R q) from (by
                                          unfold nb096_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0105 D R q) 1))))
                                      (TAlphaVar.there (show (nb096_alpha_dummy_102 D R) ≠
        (nb096_alpha_dummy_135 D R) from (by
          unfold nb096_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0134 D R) 0)))) (show (nb096_alpha_dummy_104 D R q) ≠
        (nb096_alpha_dummy_136 D R q) from (by
          unfold nb096_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0135 D R q) 0)))) (TAlphaVar.there (show
        (nb096_alpha_dummy_102 D R) ≠ (nb096_alpha_dummy_133 D R) from (by
          unfold nb096_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0132 D R) 0)))) (show (nb096_alpha_dummy_104 D R q) ≠
        (nb096_alpha_dummy_134 D R q) from (by
          unfold nb096_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0133 D R q) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb096_alpha_dummy_102 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb096_alpha_dummy_104 D R q))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_116 D R) from
        (by
          unfold nb096_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  1)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_119 D R q) from
        (by
          unfold nb096_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_115 D R) from (by
          unfold nb096_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_118 D R q) from
        (by
          unfold nb096_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold
            nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold
            nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_116
        D R) ≠ (nb096_alpha_dummy_127 D R) from (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_116
        D R) ≠ (nb096_alpha_dummy_127 D R) from (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠ (nb096_alpha_dummy_129 D R) from
        (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_129 D R) from (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_113 D R) from
        (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_135 D R), (nb096_alpha_dummy_136 D R q)),
        ((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb096_alpha_dummy_133 D R), (nb096_alpha_dummy_134 D R q)),
                    ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
                    ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
                    ((nb096_alpha_dummy_131 D R), (nb096_alpha_dummy_132 D R q)),
                    ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
                    ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
                    ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
                    ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                    ((nb096_alpha_dummy_000 D R), q),
                    ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


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
noncomputable def nb096_split_alpha_0006 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_105 D R)) (syn_ccompl
            (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_105 D R)) (syn_ccompl
              (Class.cab (nb096_alpha_dummy_101 D R) (syn_wrex (nb096_alpha_dummy_102 D R)
                  (Class.cv (nb096_alpha_dummy_041 D R))
                  (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                    (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096_alpha_dummy_106 D R q)) (syn_ccompl
            (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
                (Class.cv (nb096_alpha_dummy_044 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096_alpha_dummy_106 D R q)) (syn_ccompl
              (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
                  (Class.cv (nb096_alpha_dummy_043 D R q))
                  (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                    (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_102 D R) from
                            (by
                              unfold nb096_alpha_dummy_102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0098 D R) 1)))) (show
                            (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_104 D R q) from
                            (by
                              unfold nb096_alpha_dummy_104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
                          (TAlphaVar.there (show
                              (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_101 D R) from (by
                                unfold nb096_alpha_dummy_101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0098 D R) 0)))) (show
                              (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_103 D R q) from
                              (by
                                unfold nb096_alpha_dummy_103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0100 D R q)
                                        0)))) (TAlphaVar.there (show
                                (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_107 D R) from
                                (by
                                  unfold nb096_alpha_dummy_107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0102 D R)
                                          0)))) (show (nb096_alpha_dummy_044 D R q) ≠
                                  (nb096_alpha_dummy_108 D R q) from (by
                                  unfold nb096_alpha_dummy_108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0103 D R q)
                                          0)))) (TAlphaVar.there (show
                                  (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_105 D R) from
                                  (by
                                    unfold nb096_alpha_dummy_105;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0099 D R)
                                            0)))) (show (nb096_alpha_dummy_044 D R q) ≠
                                    (nb096_alpha_dummy_106 D R q) from (by
                                    unfold nb096_alpha_dummy_106;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0101 D R q)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
                              ((Class.cv (nb096_alpha_dummy_041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
                              ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb096_alpha_dummy_102 D R) ≠ (nb096_alpha_dummy_109 D R)
                                    from (by
                                      unfold nb096_alpha_dummy_109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0104 D R)
                                              0)))) (show (nb096_alpha_dummy_104 D R q) ≠
                                      (nb096_alpha_dummy_111 D R q) from (by
                                      unfold nb096_alpha_dummy_111;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0105 D R q) 0))))
                                  (TAlphaVar.there (show (nb096_alpha_dummy_102 D R) ≠
                                        (nb096_alpha_dummy_110 D R) from (by
                                        unfold nb096_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 1)))) (show
                                      (nb096_alpha_dummy_104 D R q) ≠
                                        (nb096_alpha_dummy_112 D R q) from (by
                                        unfold nb096_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb096_alpha_dummy_102 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_116 D R) from (by
          unfold nb096_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108 D
                    R)
                  1)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_119 D R q) from
        (by
          unfold nb096_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109 D
                    R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_115 D R) from (by
          unfold nb096_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_118 D R q) from
        (by
          unfold nb096_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111
        D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_127 D R) from
        (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_116
        D R) ≠ (nb096_alpha_dummy_127 D R) from (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠ (nb096_alpha_dummy_129 D R) from
        (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_129 D R) from (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_102 D R) from
                            (by
                              unfold nb096_alpha_dummy_102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0098 D R) 1)))) (show
                            (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_104 D R q) from
                            (by
                              unfold nb096_alpha_dummy_104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
                          (TAlphaVar.there (show
                              (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_101 D R) from (by
                                unfold nb096_alpha_dummy_101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0098 D R) 0)))) (show
                              (nb096_alpha_dummy_044 D R q) ≠ (nb096_alpha_dummy_103 D R q) from
                              (by
                                unfold nb096_alpha_dummy_103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0100 D R q)
                                        0)))) (TAlphaVar.there (show
                                (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_107 D R) from
                                (by
                                  unfold nb096_alpha_dummy_107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0102 D R)
                                          0)))) (show (nb096_alpha_dummy_044 D R q) ≠
                                  (nb096_alpha_dummy_108 D R q) from (by
                                  unfold nb096_alpha_dummy_108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0103 D R q)
                                          0)))) (TAlphaVar.there (show
                                  (nb096_alpha_dummy_042 D R) ≠ (nb096_alpha_dummy_105 D R) from
                                  (by
                                    unfold nb096_alpha_dummy_105;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0099 D R)
                                            0)))) (show (nb096_alpha_dummy_044 D R q) ≠
                                    (nb096_alpha_dummy_106 D R q) from (by
                                    unfold nb096_alpha_dummy_106;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0101 D R q)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
                              ((Class.cv (nb096_alpha_dummy_041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
                              ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb096_alpha_dummy_102 D R) ≠ (nb096_alpha_dummy_109 D R)
                                    from (by
                                      unfold nb096_alpha_dummy_109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0104 D R)
                                              0)))) (show (nb096_alpha_dummy_104 D R q) ≠
                                      (nb096_alpha_dummy_111 D R q) from (by
                                      unfold nb096_alpha_dummy_111;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0105 D R q) 0))))
                                  (TAlphaVar.there (show (nb096_alpha_dummy_102 D R) ≠
                                        (nb096_alpha_dummy_110 D R) from (by
                                        unfold nb096_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 1)))) (show
                                      (nb096_alpha_dummy_104 D R q) ≠
                                        (nb096_alpha_dummy_112 D R q) from (by
                                        unfold nb096_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb096_alpha_dummy_102 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb096_alpha_dummy_104 D R q))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_116 D R) from (by
          unfold nb096_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108 D
                    R)
                  1)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_119 D R q) from
        (by
          unfold nb096_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109 D
                    R q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_115 D R) from (by
          unfold nb096_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_118 D R q) from
        (by
          unfold nb096_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096_alpha_dummy_111 D R q) ≠ (nb096_alpha_dummy_114 D R q) from
        (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_123 D R) from
        (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_123 D R) from (by
          unfold
            nb096_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_124 D R q) from
        (by
          unfold
            nb096_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_121 D R) from (by
          unfold
            nb096_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_122 D R q) from
        (by
          unfold
            nb096_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_117 D R), (nb096_alpha_dummy_120 D R q)),
        ((nb096_alpha_dummy_116 D R), (nb096_alpha_dummy_119 D R q)),
        ((nb096_alpha_dummy_115 D R), (nb096_alpha_dummy_118 D R q)),
        ((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096_alpha_dummy_109 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111
        D R q))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠ (nb096_alpha_dummy_127 D R) from
        (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_116
        D R) ≠ (nb096_alpha_dummy_127 D R) from (by
          unfold
            nb096_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_128 D R q) from
        (by
          unfold
            nb096_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_116 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_119 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_109
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_111 D R q))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠ (nb096_alpha_dummy_129 D R) from
        (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_117
        D R) ≠ (nb096_alpha_dummy_129 D R) from (by
          unfold
            nb096_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_130 D R q) from
        (by
          unfold
            nb096_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_117 D R) ≠
        (nb096_alpha_dummy_125 D R) from (by
          unfold
            nb096_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_120 D R q) ≠ (nb096_alpha_dummy_126 D R q) from
        (by
          unfold
            nb096_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096_alpha_dummy_109 D R) ≠
        (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb096_alpha_dummy_109 D R) ≠ (nb096_alpha_dummy_113 D R) from (by
          unfold nb096_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096_alpha_dummy_111 D R q) ≠
        (nb096_alpha_dummy_114 D R q) from (by
          unfold nb096_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_113 D R), (nb096_alpha_dummy_114 D R q)),
        ((nb096_alpha_dummy_109 D R), (nb096_alpha_dummy_111 D R q)),
        ((nb096_alpha_dummy_110 D R), (nb096_alpha_dummy_112 D R q)),
        ((nb096_alpha_dummy_102 D R), (nb096_alpha_dummy_104 D R q)),
        ((nb096_alpha_dummy_101 D R), (nb096_alpha_dummy_103 D R q)),
        ((nb096_alpha_dummy_107 D R), (nb096_alpha_dummy_108 D R q)),
        ((nb096_alpha_dummy_105 D R), (nb096_alpha_dummy_106 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb096_split_alpha_0005 D R q)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb096_split_alpha_0005 D R q)))))))))))

theorem nb096_wpp_notmem_0352 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_042, fv_syn_cen] using (nb096_compact_fv_empty_0062 D R)

theorem nb096_wpp_notmem_0353 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_044, fv_syn_cen] using (nb096_compact_fv_empty_0063 D R q)

theorem nb096_wpp_notmem_0354 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_041, fv_syn_cen] using (nb096_compact_fv_empty_0064 D R)

theorem nb096_wpp_notmem_0355 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_043, fv_syn_cen] using (nb096_compact_fv_empty_0065 D R q)

theorem nb096_wpp_notmem_0356 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_001, fv_syn_cen] using (nb096_compact_fv_empty_0020 D R)

theorem nb096_wpp_notmem_0357 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_002, fv_syn_cen] using (nb096_compact_fv_empty_0021 D R q)

theorem nb096_wpp_notmem_0358 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_000, fv_syn_cen] using (nb096_compact_fv_empty_0022 D R)

theorem nb096_wpp_notmem_0359 (q : Var) : q ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb096_compact_fv_empty_0023 q)

theorem nb096_wpp_notmem_0360 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_003, fv_syn_cen] using (nb096_compact_fv_empty_0024 D R)

theorem nb096_wpp_notmem_0361 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉ ((syn_cen)).fv := by
  simpa only [nb096_alpha_dummy_004, fv_syn_cen] using (nb096_compact_fv_empty_0025 D R q)

theorem nb096_compact_envfresh_0024 (D : Class) (R : Class) (q : Var) :
    TEnvFresh
      [((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      ((syn_cen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q)
      (nb096_wpp_notmem_0352 D R) (nb096_wpp_notmem_0353 D R q)
      (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q)
        (nb096_wpp_notmem_0354 D R) (nb096_wpp_notmem_0355 D R q)
        (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R) (nb096_alpha_dummy_002 D R q)
          (nb096_wpp_notmem_0356 D R) (nb096_wpp_notmem_0357 D R q)
          (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q (nb096_wpp_notmem_0358 D R)
            (nb096_wpp_notmem_0359 q)
            (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R) (nb096_alpha_dummy_004 D R q)
              (nb096_wpp_notmem_0360 D R) (nb096_wpp_notmem_0361 D R q)
              (TEnvFresh.nil ((syn_cen)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
