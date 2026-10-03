/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C091M3BPart007Stage1


/-! NF weak partition development: NAR4H5C091M3BPart007. -/


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
noncomputable def nb091_wpp_refl_0033 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TReflOn
      [((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
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
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0036 D R p dv_R_p)

@[expose]
noncomputable def nb091_split_alpha_0011 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
        (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))) (syn_csn (syn_c0c))))
      (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
        (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))) (syn_csn (syn_c0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                          (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
          (by decide)) (freshVar_injective (((syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_048 D R) ≠
                                    (nb091_alpha_dummy_155 D R) from (by
                                    unfold nb091_alpha_dummy_155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                            0)))) (show (nb091_alpha_dummy_050 D R p) ≠
                                    (nb091_alpha_dummy_157 D R p) from (by
                                    unfold nb091_alpha_dummy_157;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0155 D R p)
                                            0)))) (TAlphaVar.there (show
                                    (nb091_alpha_dummy_048 D R) ≠ (nb091_alpha_dummy_156 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_156;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                              1)))) (show (nb091_alpha_dummy_050 D R p) ≠
                                      (nb091_alpha_dummy_158 D R p) from (by
                                      unfold nb091_alpha_dummy_158;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0155 D R p) 1))))
                                  (TAlphaVar.there (show (nb091_alpha_dummy_048 D R) ≠
                                        (nb091_alpha_dummy_181 D R) from (by
                                        unfold nb091_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0180 D R) 0)))) (show
                                      (nb091_alpha_dummy_050 D R p) ≠
                                        (nb091_alpha_dummy_182 D R p) from (by
                                        unfold nb091_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0181 D R p) 0))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_048 D R) ≠
        (nb091_alpha_dummy_179 D R) from (by
                                          unfold nb091_alpha_dummy_179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0178 D R) 0)))) (show
                                        (nb091_alpha_dummy_050 D R p) ≠
        (nb091_alpha_dummy_180 D R p) from (by
                                          unfold nb091_alpha_dummy_180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0179 D R p) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb091_alpha_dummy_048 D R))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_162 D R) from (by
          unfold nb091_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D R)
                  1)))) (show (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_165 D R p) from
        (by
          unfold nb091_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_155 D R) ≠
        (nb091_alpha_dummy_161 D R) from (by
          unfold nb091_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D
                    R)
                  0)))) (show (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_164 D R p) from
        (by
          unfold nb091_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_155 D R) ≠
        (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156
                    D R)
                  0)))) (show (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_160 D R p) from
        (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_163 D R), (nb091_alpha_dummy_166 D R p)),
        ((nb091_alpha_dummy_162 D R), (nb091_alpha_dummy_165 D R p)),
        ((nb091_alpha_dummy_161 D R), (nb091_alpha_dummy_164 D R p)),
        ((nb091_alpha_dummy_159 D R), (nb091_alpha_dummy_160 D R p)),
        ((nb091_alpha_dummy_155 D R), (nb091_alpha_dummy_157 D R p)),
        ((nb091_alpha_dummy_156 D R), (nb091_alpha_dummy_158 D R p)),
        ((nb091_alpha_dummy_181 D R), (nb091_alpha_dummy_182 D R p)),
        ((nb091_alpha_dummy_179 D R), (nb091_alpha_dummy_180 D R p)),
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
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_163 D R), (nb091_alpha_dummy_166 D R p)),
        ((nb091_alpha_dummy_162 D R), (nb091_alpha_dummy_165 D R p)),
        ((nb091_alpha_dummy_161 D R), (nb091_alpha_dummy_164 D R p)),
        ((nb091_alpha_dummy_159 D R), (nb091_alpha_dummy_160 D R p)),
        ((nb091_alpha_dummy_155 D R), (nb091_alpha_dummy_157 D R p)),
        ((nb091_alpha_dummy_156 D R), (nb091_alpha_dummy_158 D R p)),
        ((nb091_alpha_dummy_181 D R), (nb091_alpha_dummy_182 D R p)),
        ((nb091_alpha_dummy_179 D R), (nb091_alpha_dummy_180 D R p)),
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
        (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_157 D
        R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_173 D R) from
        (by
          unfold
            nb091_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_174 D R p) from
        (by
          unfold
            nb091_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_173 D R) from
        (by
          unfold
            nb091_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_174 D R p) from
        (by
          unfold
            nb091_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_175 D R) from (by
          unfold
            nb091_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_176 D R p) from
        (by
          unfold
            nb091_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_163
        D R) ≠ (nb091_alpha_dummy_175 D R) from (by
          unfold
            nb091_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_176 D R p) from
        (by
          unfold
            nb091_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091_alpha_dummy_157 D R p) ≠
        (nb091_alpha_dummy_160 D R p) from (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_159 D R),
        (nb091_alpha_dummy_160 D R p)), ((nb091_alpha_dummy_155 D R),
        (nb091_alpha_dummy_157 D R p)), ((nb091_alpha_dummy_156 D R),
        (nb091_alpha_dummy_158 D R p)), ((nb091_alpha_dummy_181 D R),
        (nb091_alpha_dummy_182 D R p)), ((nb091_alpha_dummy_179 D R),
        (nb091_alpha_dummy_180 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R),
        (nb091_alpha_dummy_178 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091_alpha_dummy_155 D R) ≠
        (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091_alpha_dummy_157 D R p) ≠
        (nb091_alpha_dummy_160 D R p) from (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091_alpha_dummy_157 D R p) ≠
        (nb091_alpha_dummy_160 D R p) from (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_159 D R),
        (nb091_alpha_dummy_160 D R p)), ((nb091_alpha_dummy_155 D R),
        (nb091_alpha_dummy_157 D R p)), ((nb091_alpha_dummy_156 D R),
        (nb091_alpha_dummy_158 D R p)), ((nb091_alpha_dummy_181 D R),
        (nb091_alpha_dummy_182 D R p)), ((nb091_alpha_dummy_179 D R),
        (nb091_alpha_dummy_180 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R),
        (nb091_alpha_dummy_178 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_048 D R) ≠
                                    (nb091_alpha_dummy_155 D R) from (by
                                    unfold nb091_alpha_dummy_155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                            0)))) (show (nb091_alpha_dummy_050 D R p) ≠
                                    (nb091_alpha_dummy_157 D R p) from (by
                                    unfold nb091_alpha_dummy_157;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0155 D R p)
                                            0)))) (TAlphaVar.there (show
                                    (nb091_alpha_dummy_048 D R) ≠ (nb091_alpha_dummy_156 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_156;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0154 D R)
                                              1)))) (show (nb091_alpha_dummy_050 D R p) ≠
                                      (nb091_alpha_dummy_158 D R p) from (by
                                      unfold nb091_alpha_dummy_158;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0155 D R p) 1))))
                                  (TAlphaVar.there (show (nb091_alpha_dummy_048 D R) ≠
                                        (nb091_alpha_dummy_181 D R) from (by
                                        unfold nb091_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0180 D R) 0)))) (show
                                      (nb091_alpha_dummy_050 D R p) ≠
                                        (nb091_alpha_dummy_182 D R p) from (by
                                        unfold nb091_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0181 D R p) 0))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_048 D R) ≠
        (nb091_alpha_dummy_179 D R) from (by
                                          unfold nb091_alpha_dummy_179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0178 D R) 0)))) (show
                                        (nb091_alpha_dummy_050 D R p) ≠
        (nb091_alpha_dummy_180 D R p) from (by
                                          unfold nb091_alpha_dummy_180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0179 D R p) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb091_alpha_dummy_048 D R))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_162 D R) from (by
          unfold nb091_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D R)
                  1)))) (show (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_165 D R p) from
        (by
          unfold nb091_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_155 D R) ≠
        (nb091_alpha_dummy_161 D R) from (by
          unfold nb091_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0158 D
                    R)
                  0)))) (show (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_164 D R p) from
        (by
          unfold nb091_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0159 D
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_155 D R) ≠
        (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156
                    D R)
                  0)))) (show (nb091_alpha_dummy_157 D R p) ≠ (nb091_alpha_dummy_160 D R p) from
        (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_163 D R), (nb091_alpha_dummy_166 D R p)),
        ((nb091_alpha_dummy_162 D R), (nb091_alpha_dummy_165 D R p)),
        ((nb091_alpha_dummy_161 D R), (nb091_alpha_dummy_164 D R p)),
        ((nb091_alpha_dummy_159 D R), (nb091_alpha_dummy_160 D R p)),
        ((nb091_alpha_dummy_155 D R), (nb091_alpha_dummy_157 D R p)),
        ((nb091_alpha_dummy_156 D R), (nb091_alpha_dummy_158 D R p)),
        ((nb091_alpha_dummy_181 D R), (nb091_alpha_dummy_182 D R p)),
        ((nb091_alpha_dummy_179 D R), (nb091_alpha_dummy_180 D R p)),
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
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0162
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0163
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0160
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0161
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠ (nb091_alpha_dummy_169 D R) from
        (by
          unfold
            nb091_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0166
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_170 D R p) from
        (by
          unfold
            nb091_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0167
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_167 D R) from (by
          unfold
            nb091_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0164
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_168 D R p) from
        (by
          unfold
            nb091_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0165
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_163 D R), (nb091_alpha_dummy_166 D R p)),
        ((nb091_alpha_dummy_162 D R), (nb091_alpha_dummy_165 D R p)),
        ((nb091_alpha_dummy_161 D R), (nb091_alpha_dummy_164 D R p)),
        ((nb091_alpha_dummy_159 D R), (nb091_alpha_dummy_160 D R p)),
        ((nb091_alpha_dummy_155 D R), (nb091_alpha_dummy_157 D R p)),
        ((nb091_alpha_dummy_156 D R), (nb091_alpha_dummy_158 D R p)),
        ((nb091_alpha_dummy_181 D R), (nb091_alpha_dummy_182 D R p)),
        ((nb091_alpha_dummy_179 D R), (nb091_alpha_dummy_180 D R p)),
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
        (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_157 D
        R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_173 D R) from
        (by
          unfold
            nb091_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_174 D R p) from
        (by
          unfold
            nb091_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠ (nb091_alpha_dummy_173 D R) from
        (by
          unfold
            nb091_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0170
                    D R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_174 D R p) from
        (by
          unfold
            nb091_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0171
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_162 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0168
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_165 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0169
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_155
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_175 D R) from (by
          unfold
            nb091_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_176 D R p) from
        (by
          unfold
            nb091_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_163
        D R) ≠ (nb091_alpha_dummy_175 D R) from (by
          unfold
            nb091_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0174
                    D R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_176 D R p) from
        (by
          unfold
            nb091_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0175
                    D R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_163 D R) ≠
        (nb091_alpha_dummy_171 D R) from (by
          unfold
            nb091_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0172
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_166 D R p) ≠ (nb091_alpha_dummy_172 D R p) from
        (by
          unfold
            nb091_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0173
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091_alpha_dummy_157 D R p) ≠
        (nb091_alpha_dummy_160 D R p) from (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_159 D R),
        (nb091_alpha_dummy_160 D R p)), ((nb091_alpha_dummy_155 D R),
        (nb091_alpha_dummy_157 D R p)), ((nb091_alpha_dummy_156 D R),
        (nb091_alpha_dummy_158 D R p)), ((nb091_alpha_dummy_181 D R),
        (nb091_alpha_dummy_182 D R p)), ((nb091_alpha_dummy_179 D R),
        (nb091_alpha_dummy_180 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R),
        (nb091_alpha_dummy_178 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb091_alpha_dummy_155 D R) ≠
        (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091_alpha_dummy_157 D R p) ≠
        (nb091_alpha_dummy_160 D R p) from (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_155 D R) ≠ (nb091_alpha_dummy_159 D R) from (by
          unfold nb091_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0156 D R) 0)))) (show (nb091_alpha_dummy_157 D R p) ≠
        (nb091_alpha_dummy_160 D R p) from (by
          unfold nb091_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0157 D R p) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_159 D R),
        (nb091_alpha_dummy_160 D R p)), ((nb091_alpha_dummy_155 D R),
        (nb091_alpha_dummy_157 D R p)), ((nb091_alpha_dummy_156 D R),
        (nb091_alpha_dummy_158 D R p)), ((nb091_alpha_dummy_181 D R),
        (nb091_alpha_dummy_182 D R p)), ((nb091_alpha_dummy_179 D R),
        (nb091_alpha_dummy_180 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R),
        (nb091_alpha_dummy_178 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_closed
              [((nb091_alpha_dummy_179 D R), (nb091_alpha_dummy_180 D R p)),
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
              (syn_ccompl (syn_csn (syn_c0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))


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
noncomputable def nb091_split_alpha_0012 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) (dv_R_p : p ∉ R.fv) :
    TAlphaWff
      [((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_177 D R))
          (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_177 D R))
            (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_178 D R p))
          (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_178 D R p))
            (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_reflOn [((nb091_alpha_dummy_103 D R),
                                    (nb091_alpha_dummy_104 D R p)),
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
                                D (nb091_focused_refl_0002 D R p dv_D_p)))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((syn_cuni (Class.cv
        (nb091_alpha_dummy_000 D R)))).fv) (by decide)) (freshVar_injective
        (((syn_cuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_116 D R) from (by
          unfold
            nb091_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_118 p) from (by
          unfold
            nb091_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_115 D R) from (by
          unfold
            nb091_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_117 p) from (by
          unfold
            nb091_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_112 D R) from (by
          unfold
            nb091_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_114 p) from (by
          unfold
            nb091_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_111 D R) from (by
          unfold
            nb091_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_113 p) from (by
          unfold
            nb091_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_109 D R) from (by
          unfold
            nb091_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_110 p) from (by
          unfold
            nb091_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_106 D R) from (by
          unfold
            nb091_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_108 R p) from (by
          unfold
            nb091_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_105 D R) from (by
          unfold
            nb091_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_107 R p) from (by
          unfold
            nb091_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_103 D R) from (by
          unfold
            nb091_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_104 D R p) from (by
          unfold
            nb091_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_101 D R) from (by
          unfold
            nb091_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_102 D R p) from (by
          unfold
            nb091_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_048 D R) from (by
          unfold
            nb091_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
          unfold
            nb091_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_047 D R) from (by
          unfold
            nb091_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold
            nb091_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_177 D R) from (by
          unfold
            nb091_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_178 D R p) from (by
          unfold
            nb091_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_051 D R) from (by
          unfold
            nb091_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_052 D R p) from (by
          unfold
            nb091_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_045 D R) from (by
          unfold
            nb091_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_046 D R p) from (by
          unfold
            nb091_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_042 D R) from (by
          unfold
            nb091_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_044 D R p) from (by
          unfold
            nb091_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_041 D R) from (by
          unfold
            nb091_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_043 D R p) from (by
          unfold
            nb091_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_001 D R) from (by
          unfold
            nb091_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
          unfold
            nb091_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                        [((nb091_alpha_dummy_106 D R),
        (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R),
        (nb091_alpha_dummy_107 R p)), ((nb091_alpha_dummy_103 D R),
        (nb091_alpha_dummy_104 D R p)), ((nb091_alpha_dummy_101 D R),
        (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R),
        (nb091_alpha_dummy_178 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_ccnv (syn_cdif R (syn_cid)))
                                        (nb091_wpp_refl_0033 D R p dv_R_p)))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_reflOn [((nb091_alpha_dummy_103 D R),
                                    (nb091_alpha_dummy_104 D R p)),
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
                                D (nb091_focused_refl_0002 D R p dv_D_p)))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((syn_cuni (Class.cv
        (nb091_alpha_dummy_000 D R)))).fv) (by decide)) (freshVar_injective
        (((syn_cuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_116 D R) from (by
          unfold
            nb091_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_118 p) from (by
          unfold
            nb091_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_115 D R) from (by
          unfold
            nb091_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_117 p) from (by
          unfold
            nb091_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_112 D R) from (by
          unfold
            nb091_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_114 p) from (by
          unfold
            nb091_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_111 D R) from (by
          unfold
            nb091_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_113 p) from (by
          unfold
            nb091_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_109 D R) from (by
          unfold
            nb091_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_110 p) from (by
          unfold
            nb091_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_106 D R) from (by
          unfold
            nb091_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_108 R p) from (by
          unfold
            nb091_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_105 D R) from (by
          unfold
            nb091_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_107 R p) from (by
          unfold
            nb091_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_103 D R) from (by
          unfold
            nb091_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_104 D R p) from (by
          unfold
            nb091_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_101 D R) from (by
          unfold
            nb091_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_102 D R p) from (by
          unfold
            nb091_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_048 D R) from (by
          unfold
            nb091_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
          unfold
            nb091_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_047 D R) from (by
          unfold
            nb091_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold
            nb091_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_177 D R) from (by
          unfold
            nb091_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_178 D R p) from (by
          unfold
            nb091_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_051 D R) from (by
          unfold
            nb091_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_052 D R p) from (by
          unfold
            nb091_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_045 D R) from (by
          unfold
            nb091_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_046 D R p) from (by
          unfold
            nb091_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_042 D R) from (by
          unfold
            nb091_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_044 D R p) from (by
          unfold
            nb091_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_041 D R) from (by
          unfold
            nb091_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_043 D R p) from (by
          unfold
            nb091_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_001 D R) from (by
          unfold
            nb091_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
          unfold
            nb091_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                        [((nb091_alpha_dummy_106 D R),
        (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R),
        (nb091_alpha_dummy_107 R p)), ((nb091_alpha_dummy_103 D R),
        (nb091_alpha_dummy_104 D R p)), ((nb091_alpha_dummy_101 D R),
        (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R),
        (nb091_alpha_dummy_178 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_ccnv (syn_cdif R (syn_cid)))
                                        (nb091_wpp_refl_0033 D R p dv_R_p)))))))))))))))
            (nb091_split_alpha_0011 D R p))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_reflOn [((nb091_alpha_dummy_103 D R),
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
                                  D (nb091_focused_refl_0002 D R p dv_D_p)))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
        (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) (by decide))
        (freshVar_injective (((syn_cuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_116 D R) from (by
          unfold
            nb091_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_118 p) from (by
          unfold
            nb091_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_115 D R) from (by
          unfold
            nb091_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_117 p) from (by
          unfold
            nb091_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_112 D R) from (by
          unfold
            nb091_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_114 p) from (by
          unfold
            nb091_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_111 D R) from (by
          unfold
            nb091_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_113 p) from (by
          unfold
            nb091_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_109 D R) from (by
          unfold
            nb091_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_110 p) from (by
          unfold
            nb091_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_106 D R) from (by
          unfold
            nb091_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_108 R p) from (by
          unfold
            nb091_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_105 D R) from (by
          unfold
            nb091_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_107 R p) from (by
          unfold
            nb091_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_103 D R) from (by
          unfold
            nb091_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_104 D R p) from (by
          unfold
            nb091_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_101 D R) from (by
          unfold
            nb091_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_102 D R p) from (by
          unfold
            nb091_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_048 D R) from (by
          unfold
            nb091_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
          unfold
            nb091_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_047 D R) from (by
          unfold
            nb091_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold
            nb091_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_177 D R) from (by
          unfold
            nb091_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_178 D R p) from (by
          unfold
            nb091_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_051 D R) from (by
          unfold
            nb091_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_052 D R p) from (by
          unfold
            nb091_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_045 D R) from (by
          unfold
            nb091_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_046 D R p) from (by
          unfold
            nb091_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_042 D R) from (by
          unfold
            nb091_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_044 D R p) from (by
          unfold
            nb091_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_041 D R) from (by
          unfold
            nb091_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_043 D R p) from (by
          unfold
            nb091_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_001 D R) from (by
          unfold
            nb091_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
          unfold
            nb091_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
        [((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
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
        (nb091_alpha_dummy_004 D R p))] (syn_ccnv (syn_cdif R (syn_cid)))
        (nb091_wpp_refl_0033 D R p dv_R_p)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_reflOn [((nb091_alpha_dummy_103 D R),
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
                                  D (nb091_focused_refl_0002 D R p dv_D_p)))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
        (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) (by decide))
        (freshVar_injective (((syn_cuni (Class.cv p))).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_000 D R))).fv) (by decide))
        (freshVar_injective (((Class.cv p)).fv) (by decide)) (TAlphaVar.here _ _ _))
        (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_116 D R) from (by
          unfold
            nb091_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_118 p) from (by
          unfold
            nb091_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_115 D R) from (by
          unfold
            nb091_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0114
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_117 p) from (by
          unfold
            nb091_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0115
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_112 D R) from (by
          unfold
            nb091_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  1)))) (show p ≠ (nb091_alpha_dummy_114 p) from (by
          unfold
            nb091_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_111 D R) from (by
          unfold
            nb091_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0112
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_113 p) from (by
          unfold
            nb091_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0113
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_109 D R) from (by
          unfold
            nb091_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0110
                    D R)
                  0)))) (show p ≠ (nb091_alpha_dummy_110 p) from (by
          unfold
            nb091_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0111
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_106 D R) from (by
          unfold
            nb091_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_108 R p) from (by
          unfold
            nb091_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_105 D R) from (by
          unfold
            nb091_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0108
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_107 R p) from (by
          unfold
            nb091_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0109
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_103 D R) from (by
          unfold
            nb091_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0106
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_104 D R p) from (by
          unfold
            nb091_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0107
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_101 D R) from (by
          unfold
            nb091_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0104
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_102 D R p) from (by
          unfold
            nb091_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0105
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_048 D R) from (by
          unfold
            nb091_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
          unfold
            nb091_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_047 D R) from (by
          unfold
            nb091_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0090
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold
            nb091_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0092
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_177 D R) from (by
          unfold
            nb091_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0176
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_178 D R p) from (by
          unfold
            nb091_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0177
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_051 D R) from (by
          unfold
            nb091_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0091
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_052 D R p) from (by
          unfold
            nb091_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0093
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_045 D R) from (by
          unfold
            nb091_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0088
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_046 D R p) from (by
          unfold
            nb091_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0089
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_042 D R) from (by
          unfold
            nb091_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  1)))) (show p ≠ (nb091_alpha_dummy_044 D R p) from (by
          unfold
            nb091_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_041 D R) from (by
          unfold
            nb091_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0086
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_043 D R p) from (by
          unfold
            nb091_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0087
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_000 D R) ≠
        (nb091_alpha_dummy_001 D R) from (by
          unfold
            nb091_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0004
                    D
                    R)
                  0)))) (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
          unfold
            nb091_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0005
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0009 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_105
        D R) ≠ (nb091_alpha_dummy_120 D R) from (by
          unfold
            nb091_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  1)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
          unfold
            nb091_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_119 D R) from (by
          unfold
            nb091_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0144
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold
            nb091_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0146
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_149 D R) from (by
          unfold
            nb091_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0148
                    D R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_150 R p) from (by
          unfold
            nb091_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0149
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_105 D R) ≠
        (nb091_alpha_dummy_123 D R) from (by
          unfold
            nb091_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0145
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
          unfold
            nb091_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0147
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D
        R)))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪ ((Class.cv (nb091_alpha_dummy_105
        D R))).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_108
        R p))).fv ∪ ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb091_split_alpha_0010 D R p))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120
        D R), (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121
        R p)), ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106
        D R), (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107
        R p)), ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_048
        D R), (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_177 D R), (nb091_alpha_dummy_178
        D R p)), ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042
        D R), (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002
        D R p)), ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
        [((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
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
        (nb091_alpha_dummy_004 D R p))] (syn_ccnv (syn_cdif R (syn_cid)))
        (nb091_wpp_refl_0033 D R p dv_R_p))))))))))))))) (nb091_split_alpha_0011 D R p)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
