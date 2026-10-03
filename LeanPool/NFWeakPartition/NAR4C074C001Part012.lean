/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C074C001Block003

/-! NF weak partition development: NAR4C074C001Part012. -/


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
noncomputable def nb074_split_alpha_0008 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_155), (nb074_alpha_dummy_156 x)),
        ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
        ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
        ((nb074_alpha_dummy_153), (nb074_alpha_dummy_154 x)),
        ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
        ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_155))
          (syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_155)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_156 x))
          (syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_156 x))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_131) from (by
                              unfold nb074_alpha_dummy_131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0130) 0))))
                          (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_133 x) from (by
                              unfold nb074_alpha_dummy_133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0131 x) 0))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_132) from (by
                                unfold nb074_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0130) 1))))
                            (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_134 x) from (by
                                unfold nb074_alpha_dummy_134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0131 x) 1))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_157) from (by
                                  unfold nb074_alpha_dummy_157;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0160) 0))))
                              (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_158 x) from
                                (by
                                  unfold nb074_alpha_dummy_158;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0161 x) 0))))
                              (TAlphaVar.there
                                (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_155) from (by
                                    unfold nb074_alpha_dummy_155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0158) 0)))) (show
                                  (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_156 x) from (by
                                    unfold nb074_alpha_dummy_156;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0159 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_124))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_126 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_138) from (by
          unfold nb074_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 1)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_141 x) from (by
          unfold nb074_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_137) from (by
          unfold nb074_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_140 x) from (by
          unfold nb074_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
          unfold nb074_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0132) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_136 x) from (by
          unfold nb074_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0133 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)), ((nb074_alpha_dummy_155),
        (nb074_alpha_dummy_156 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
        ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_153),
        (nb074_alpha_dummy_154 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)), ((nb074_alpha_dummy_155),
        (nb074_alpha_dummy_156 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
        ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_153),
        (nb074_alpha_dummy_154 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠
        (nb074_alpha_dummy_149) from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_149)
        from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠
        (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                    ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                    ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                    ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)),
                                    ((nb074_alpha_dummy_155), (nb074_alpha_dummy_156 x)),
                                    ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                    ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                    ((nb074_alpha_dummy_153), (nb074_alpha_dummy_154 x)),
                                    ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from
                                    (by
                                      unfold nb074_alpha_dummy_135;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0132)
                                              0)))) (show
                                    (nb074_alpha_dummy_133 x) ≠ (nb074_alpha_dummy_136 x) from
                                    (by
                                      unfold nb074_alpha_dummy_136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0133 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                    ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                    ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                    ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)),
                                    ((nb074_alpha_dummy_155), (nb074_alpha_dummy_156 x)),
                                    ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                    ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                    ((nb074_alpha_dummy_153), (nb074_alpha_dummy_154 x)),
                                    ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_131) from (by
                              unfold nb074_alpha_dummy_131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0130) 0))))
                          (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_133 x) from (by
                              unfold nb074_alpha_dummy_133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0131 x) 0))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_132) from (by
                                unfold nb074_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0130) 1))))
                            (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_134 x) from (by
                                unfold nb074_alpha_dummy_134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0131 x) 1))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_157) from (by
                                  unfold nb074_alpha_dummy_157;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0160) 0))))
                              (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_158 x) from
                                (by
                                  unfold nb074_alpha_dummy_158;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0161 x) 0))))
                              (TAlphaVar.there
                                (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_155) from (by
                                    unfold nb074_alpha_dummy_155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0158) 0)))) (show
                                  (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_156 x) from (by
                                    unfold nb074_alpha_dummy_156;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0159 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_124))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_126 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_138) from (by
          unfold nb074_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 1)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_141 x) from (by
          unfold nb074_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_137) from (by
          unfold nb074_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_140 x) from (by
          unfold nb074_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
          unfold nb074_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0132) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_136 x) from (by
          unfold nb074_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0133 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)), ((nb074_alpha_dummy_155),
        (nb074_alpha_dummy_156 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
        ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_153),
        (nb074_alpha_dummy_154 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)), ((nb074_alpha_dummy_155),
        (nb074_alpha_dummy_156 x)), ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
        ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_153),
        (nb074_alpha_dummy_154 x)), ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠
        (nb074_alpha_dummy_149) from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_149)
        from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠
        (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                    ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                    ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                    ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)),
                                    ((nb074_alpha_dummy_155), (nb074_alpha_dummy_156 x)),
                                    ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                    ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                    ((nb074_alpha_dummy_153), (nb074_alpha_dummy_154 x)),
                                    ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from
                                    (by
                                      unfold nb074_alpha_dummy_135;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0132)
                                              0)))) (show
                                    (nb074_alpha_dummy_133 x) ≠ (nb074_alpha_dummy_136 x) from
                                    (by
                                      unfold nb074_alpha_dummy_136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0133 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                    ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                    ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                    ((nb074_alpha_dummy_157), (nb074_alpha_dummy_158 x)),
                                    ((nb074_alpha_dummy_155), (nb074_alpha_dummy_156 x)),
                                    ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                    ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                    ((nb074_alpha_dummy_153), (nb074_alpha_dummy_154 x)),
                                    ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_155), (nb074_alpha_dummy_156 x)),
            ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
            ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
            ((nb074_alpha_dummy_153), (nb074_alpha_dummy_154 x)),
            ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
            ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
            ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
            ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
            ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
            ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
            ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
            ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nominal_df_domfn (x : Var) :
    Nominal.NPrf (.classEq (syn_cdomfn) (syn_cmpt x (syn_cvv) (syn_cdm (.cv x)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb074_split_alpha_0002 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_001) from (by
                          unfold nb074_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0004) 0))))
                      (show x ≠ (nb074_alpha_dummy_002 x) from (by
                          unfold nb074_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0005 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                      ((nb074_alpha_dummy_000), x),
                      ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                    (syn_cvv) (by simp only [fv_syn_cvv])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                              ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                              ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                              ((nb074_alpha_dummy_000), x),
                              ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                            (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                          (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.neg (nb074_split_alpha_0004 x))))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_085) from (by
          unfold nb074_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0084) 0))))) (Ne.symm (show (nb074_alpha_dummy_084 x) ≠
        (nb074_alpha_dummy_086 x) from (by
          unfold nb074_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0085 x) 0))))) (TAlphaVar.there (Ne.symm (show
        (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_085) from (by
          unfold nb074_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0082) 0))))) (Ne.symm (show (nb074_alpha_dummy_083 x) ≠
        (nb074_alpha_dummy_086 x) from (by
          unfold nb074_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0083 x) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074_split_alpha_0005 x))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠
        (nb074_alpha_dummy_088) from (by
          unfold
            nb074_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  1)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_090 x) from (by
          unfold
            nb074_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_087)
        from (by
          unfold
            nb074_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  0)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_089 x) from (by
          unfold
            nb074_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_117)
        from (by
          unfold
            nb074_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0118)
                  0)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_118 x) from (by
          unfold
            nb074_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0119
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_091)
        from (by
          unfold
            nb074_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0115)
                  0)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_092 x) from (by
          unfold
            nb074_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0117
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_081))).fv ∪
        ((Class.cv (nb074_alpha_dummy_082))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074_split_alpha_0006 x))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_088) from (by
          unfold
            nb074_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  1)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_090 x) from (by
          unfold
            nb074_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_087)
        from (by
          unfold
            nb074_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  0)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_089 x) from (by
          unfold
            nb074_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_117)
        from (by
          unfold
            nb074_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0118)
                  0)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_118 x) from (by
          unfold
            nb074_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0119
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_091)
        from (by
          unfold
            nb074_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0115)
                  0)))) (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_092 x) from (by
          unfold
            nb074_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0117
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_081))).fv ∪
        ((Class.cv (nb074_alpha_dummy_082))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074_split_alpha_0006 x))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074_split_alpha_0007 x))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠
        (nb074_alpha_dummy_124) from (by
          unfold
            nb074_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  1)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_126 x) from (by
          unfold
            nb074_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_123)
        from (by
          unfold
            nb074_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  0)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_125 x) from (by
          unfold
            nb074_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_153)
        from (by
          unfold
            nb074_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0156)
                  0)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_154 x) from (by
          unfold
            nb074_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0157
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_127)
        from (by
          unfold
            nb074_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0153)
                  0)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_128 x) from (by
          unfold
            nb074_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_082))).fv ∪
        ((Class.cv (nb074_alpha_dummy_081))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074_split_alpha_0008 x))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_124) from (by
          unfold
            nb074_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  1)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_126 x) from (by
          unfold
            nb074_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_123)
        from (by
          unfold
            nb074_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  0)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_125 x) from (by
          unfold
            nb074_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_153)
        from (by
          unfold
            nb074_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0156)
                  0)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_154 x) from (by
          unfold
            nb074_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0157
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_127)
        from (by
          unfold
            nb074_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0153)
                  0)))) (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_128 x) from (by
          unfold
            nb074_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_082))).fv ∪
        ((Class.cv (nb074_alpha_dummy_081))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074_split_alpha_0008 x)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_082) from (by
          unfold nb074_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0166) 1)))) (show x ≠ (nb074_alpha_dummy_084 x) from (by
          unfold nb074_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0167 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_081) from (by
          unfold nb074_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0166) 0)))) (show x ≠ (nb074_alpha_dummy_083 x) from (by
          unfold nb074_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0167 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_085) from (by
          unfold nb074_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0164) 0)))) (show x ≠ (nb074_alpha_dummy_086 x) from (by
          unfold nb074_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0165 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_042) from (by
          unfold nb074_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0162) 1)))) (show x ≠ (nb074_alpha_dummy_044 x) from (by
          unfold nb074_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0163 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_041) from (by
          unfold nb074_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0162) 0)))) (show x ≠ (nb074_alpha_dummy_043 x) from (by
          unfold nb074_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0163 x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_001)
        from (by
          unfold nb074_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0004)
                  0)))) (show x ≠ (nb074_alpha_dummy_002 x) from (by
          unfold nb074_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0005 x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
