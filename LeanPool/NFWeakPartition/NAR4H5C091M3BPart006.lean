/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C091M3BPart006Block001


/-! NF weak partition development: NAR4H5C091M3BPart006. -/


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
noncomputable def nb091_split_alpha_0009 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_125 D R))
          (Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_125 D R))
            (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_126 R p))
          (Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_126 R p))
            (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
                      unfold nb091_alpha_dummy_120;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
                  (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
                      unfold nb091_alpha_dummy_122;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0118 R p) 1)))) (TAlphaVar.there
                    (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
                        unfold nb091_alpha_dummy_119;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
                    (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
                        unfold nb091_alpha_dummy_121;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_125 D R) from (by
                          unfold nb091_alpha_dummy_125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0120 D R) 0))))
                      (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_126 R p) from (by
                          unfold nb091_alpha_dummy_126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0121 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_123 D R) from (by
                            unfold nb091_alpha_dummy_123;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0117 D R) 0))))
                        (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
                            unfold nb091_alpha_dummy_124;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0119 R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_105 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_127 D R) from
                            (by
                              unfold nb091_alpha_dummy_127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0122 D R) 0))))
                          (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_129 R p) from
                            (by
                              unfold nb091_alpha_dummy_129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                          (TAlphaVar.there (show
                              (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_128 D R) from (by
                                unfold nb091_alpha_dummy_128;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0122 D R) 1)))) (show
                              (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_130 R p) from (by
                                unfold nb091_alpha_dummy_130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0123 R p) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_120 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_122 R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_134 D R) from
        (by
          unfold nb091_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R) 1)))) (show (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_137 R p) from (by
          unfold nb091_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p) 1)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_133 D R) from (by
          unfold nb091_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_136 R p) from (by
          unfold nb091_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
          unfold nb091_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
          unfold nb091_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R
        p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                    ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                                    ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                                    ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                                    ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                                    ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
                                    ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                                    ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                                    ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                                    ((nb091_alpha_dummy_103 D R),
                                      (nb091_alpha_dummy_104 D R p)),
                                    ((nb091_alpha_dummy_101 D R),
                                      (nb091_alpha_dummy_102 D R p)),
                                    ((nb091_alpha_dummy_048 D R),
                                      (nb091_alpha_dummy_050 D R p)),
                                    ((nb091_alpha_dummy_047 D R),
                                      (nb091_alpha_dummy_049 D R p)),
                                    ((nb091_alpha_dummy_177 D R),
                                      (nb091_alpha_dummy_178 D R p)),
                                    ((nb091_alpha_dummy_051 D R),
                                      (nb091_alpha_dummy_052 D R p)),
                                    ((nb091_alpha_dummy_045 D R),
                                      (nb091_alpha_dummy_046 D R p)),
                                    ((nb091_alpha_dummy_042 D R),
                                      (nb091_alpha_dummy_044 D R p)),
                                    ((nb091_alpha_dummy_041 D R),
                                      (nb091_alpha_dummy_043 D R p)),
                                    ((nb091_alpha_dummy_001 D R),
                                      (nb091_alpha_dummy_002 D R p)),
                                    ((nb091_alpha_dummy_000 D R), p),
                                    ((nb091_alpha_dummy_003 D R),
                                      (nb091_alpha_dummy_004 D R p))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0124 D R)
                                              0)))) (show (nb091_alpha_dummy_129 R p) ≠
                                      (nb091_alpha_dummy_132 R p) from (by
                                      unfold nb091_alpha_dummy_132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0125 R p)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                    ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                                    ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                                    ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                                    ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                                    ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
                                    ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                                    ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                                    ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                                    ((nb091_alpha_dummy_103 D R),
                                      (nb091_alpha_dummy_104 D R p)),
                                    ((nb091_alpha_dummy_101 D R),
                                      (nb091_alpha_dummy_102 D R p)),
                                    ((nb091_alpha_dummy_048 D R),
                                      (nb091_alpha_dummy_050 D R p)),
                                    ((nb091_alpha_dummy_047 D R),
                                      (nb091_alpha_dummy_049 D R p)),
                                    ((nb091_alpha_dummy_177 D R),
                                      (nb091_alpha_dummy_178 D R p)),
                                    ((nb091_alpha_dummy_051 D R),
                                      (nb091_alpha_dummy_052 D R p)),
                                    ((nb091_alpha_dummy_045 D R),
                                      (nb091_alpha_dummy_046 D R p)),
                                    ((nb091_alpha_dummy_042 D R),
                                      (nb091_alpha_dummy_044 D R p)),
                                    ((nb091_alpha_dummy_041 D R),
                                      (nb091_alpha_dummy_043 D R p)),
                                    ((nb091_alpha_dummy_001 D R),
                                      (nb091_alpha_dummy_002 D R p)),
                                    ((nb091_alpha_dummy_000 D R), p),
                                    ((nb091_alpha_dummy_003 D R),
                                      (nb091_alpha_dummy_004 D R p))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
                        unfold nb091_alpha_dummy_120;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
                    (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
                        unfold nb091_alpha_dummy_122;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
                          unfold nb091_alpha_dummy_119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
                      (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
                          unfold nb091_alpha_dummy_121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_125 D R) from (by
                            unfold nb091_alpha_dummy_125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0120 D R) 0))))
                        (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_126 R p) from (by
                            unfold nb091_alpha_dummy_126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0121 R p) 0))))
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_123 D R) from
                            (by
                              unfold nb091_alpha_dummy_123;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0117 D R) 0))))
                          (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_124 R p) from
                            (by
                              unfold nb091_alpha_dummy_124;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0119 R p) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
                        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
                        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_127 D R) from (by
                                unfold nb091_alpha_dummy_127;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0122 D R) 0)))) (show
                              (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_129 R p) from (by
                                unfold nb091_alpha_dummy_129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                            (TAlphaVar.there (show
                                (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_128 D R) from
                                (by
                                  unfold nb091_alpha_dummy_128;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0122 D R)
                                          1)))) (show
                                (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_130 R p) from
                                (by
                                  unfold nb091_alpha_dummy_130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0123 R p)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb091_alpha_dummy_120 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb091_alpha_dummy_122 R p))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_134 D R) from (by
          unfold nb091_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  1)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_137 R p) from (by
          unfold nb091_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_133 D R) from (by
          unfold nb091_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_136 R p) from (by
          unfold nb091_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
          unfold nb091_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
          unfold nb091_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R
        p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
                                          unfold nb091_alpha_dummy_131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0124 D R) 0)))) (show
                                        (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_132 R p) from (by
                                          unfold nb091_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0125 R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                      ((nb091_alpha_dummy_127 D R),
                                        (nb091_alpha_dummy_129 R p)),
                                      ((nb091_alpha_dummy_128 D R),
                                        (nb091_alpha_dummy_130 R p)),
                                      ((nb091_alpha_dummy_120 D R),
                                        (nb091_alpha_dummy_122 R p)),
                                      ((nb091_alpha_dummy_119 D R),
                                        (nb091_alpha_dummy_121 R p)),
                                      ((nb091_alpha_dummy_125 D R),
                                        (nb091_alpha_dummy_126 R p)),
                                      ((nb091_alpha_dummy_123 D R),
                                        (nb091_alpha_dummy_124 R p)),
                                      ((nb091_alpha_dummy_106 D R),
                                        (nb091_alpha_dummy_108 R p)),
                                      ((nb091_alpha_dummy_105 D R),
                                        (nb091_alpha_dummy_107 R p)),
                                      ((nb091_alpha_dummy_103 D R),
                                        (nb091_alpha_dummy_104 D R p)),
                                      ((nb091_alpha_dummy_101 D R),
                                        (nb091_alpha_dummy_102 D R p)),
                                      ((nb091_alpha_dummy_048 D R),
                                        (nb091_alpha_dummy_050 D R p)),
                                      ((nb091_alpha_dummy_047 D R),
                                        (nb091_alpha_dummy_049 D R p)),
                                      ((nb091_alpha_dummy_177 D R),
                                        (nb091_alpha_dummy_178 D R p)),
                                      ((nb091_alpha_dummy_051 D R),
                                        (nb091_alpha_dummy_052 D R p)),
                                      ((nb091_alpha_dummy_045 D R),
                                        (nb091_alpha_dummy_046 D R p)),
                                      ((nb091_alpha_dummy_042 D R),
                                        (nb091_alpha_dummy_044 D R p)),
                                      ((nb091_alpha_dummy_041 D R),
                                        (nb091_alpha_dummy_043 D R p)),
                                      ((nb091_alpha_dummy_001 D R),
                                        (nb091_alpha_dummy_002 D R p)),
                                      ((nb091_alpha_dummy_000 D R), p),
                                      ((nb091_alpha_dummy_003 D R),
                                        (nb091_alpha_dummy_004 D R p))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
                                          unfold nb091_alpha_dummy_131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0124 D R) 0)))) (show
                                        (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_132 R p) from (by
                                          unfold nb091_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0125 R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                      ((nb091_alpha_dummy_127 D R),
                                        (nb091_alpha_dummy_129 R p)),
                                      ((nb091_alpha_dummy_128 D R),
                                        (nb091_alpha_dummy_130 R p)),
                                      ((nb091_alpha_dummy_120 D R),
                                        (nb091_alpha_dummy_122 R p)),
                                      ((nb091_alpha_dummy_119 D R),
                                        (nb091_alpha_dummy_121 R p)),
                                      ((nb091_alpha_dummy_125 D R),
                                        (nb091_alpha_dummy_126 R p)),
                                      ((nb091_alpha_dummy_123 D R),
                                        (nb091_alpha_dummy_124 R p)),
                                      ((nb091_alpha_dummy_106 D R),
                                        (nb091_alpha_dummy_108 R p)),
                                      ((nb091_alpha_dummy_105 D R),
                                        (nb091_alpha_dummy_107 R p)),
                                      ((nb091_alpha_dummy_103 D R),
                                        (nb091_alpha_dummy_104 D R p)),
                                      ((nb091_alpha_dummy_101 D R),
                                        (nb091_alpha_dummy_102 D R p)),
                                      ((nb091_alpha_dummy_048 D R),
                                        (nb091_alpha_dummy_050 D R p)),
                                      ((nb091_alpha_dummy_047 D R),
                                        (nb091_alpha_dummy_049 D R p)),
                                      ((nb091_alpha_dummy_177 D R),
                                        (nb091_alpha_dummy_178 D R p)),
                                      ((nb091_alpha_dummy_051 D R),
                                        (nb091_alpha_dummy_052 D R p)),
                                      ((nb091_alpha_dummy_045 D R),
                                        (nb091_alpha_dummy_046 D R p)),
                                      ((nb091_alpha_dummy_042 D R),
                                        (nb091_alpha_dummy_044 D R p)),
                                      ((nb091_alpha_dummy_041 D R),
                                        (nb091_alpha_dummy_043 D R p)),
                                      ((nb091_alpha_dummy_001 D R),
                                        (nb091_alpha_dummy_002 D R p)),
                                      ((nb091_alpha_dummy_000 D R), p),
                                      ((nb091_alpha_dummy_003 D R),
                                        (nb091_alpha_dummy_004 D R p))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
