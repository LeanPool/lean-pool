/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part004

/-! NF weak partition development: NAR4H5C093M3Part005. -/


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
noncomputable def nb093_split_alpha_0007 (A : Class) (r : Var) (d : Var)
    (dv_d_r : d ≠ r) :
    TAlphaWff
      [((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_050 A))
          (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
              (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_050 A))
            (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
                (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_051 r d))
          (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
              (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_051 r d))
            (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
                (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_054 A) from
                                    (by
                                      unfold nb093_alpha_dummy_054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0050 A)
                                              0)))) (show r ≠ (nb093_alpha_dummy_055 r) from (by
                                      unfold nb093_alpha_dummy_055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0051 r)
                                              0)))) (TAlphaVar.there (show
                                      (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_052 A) from
                                      (by
                                        unfold nb093_alpha_dummy_052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0048 A)
                                                0)))) (show r ≠ (nb093_alpha_dummy_053 r) from
                                      (by
                                        unfold nb093_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0049 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_045 A)
                                        from (by
                                          unfold nb093_alpha_dummy_045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0042 A) 1))))
                                      (show r ≠ (nb093_alpha_dummy_047 r d) from (by
                                          unfold nb093_alpha_dummy_047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0044 r d) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093_alpha_dummy_046 r d) from
        (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_050 A) from (by
          unfold nb093_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093_alpha_dummy_051 r d) from
        (by
          unfold nb093_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_048 A) from (by
          unfold nb093_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093_alpha_dummy_049 r d) from
        (by
          unfold nb093_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r)
        (TAlphaVar.here _ _ _))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb093_split_alpha_0006 A r d dv_d_r)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_054 A) from
                                    (by
                                      unfold nb093_alpha_dummy_054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0050 A)
                                              0)))) (show r ≠ (nb093_alpha_dummy_055 r) from (by
                                      unfold nb093_alpha_dummy_055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0051 r)
                                              0)))) (TAlphaVar.there (show
                                      (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_052 A) from
                                      (by
                                        unfold nb093_alpha_dummy_052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0048 A)
                                                0)))) (show r ≠ (nb093_alpha_dummy_053 r) from
                                      (by
                                        unfold nb093_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0049 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_045 A)
                                        from (by
                                          unfold nb093_alpha_dummy_045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0042 A) 1))))
                                      (show r ≠ (nb093_alpha_dummy_047 r d) from (by
                                          unfold nb093_alpha_dummy_047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0044 r d) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093_alpha_dummy_046 r d) from
        (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_050 A) from (by
          unfold nb093_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093_alpha_dummy_051 r d) from
        (by
          unfold nb093_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_048 A) from (by
          unfold nb093_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093_alpha_dummy_049 r d) from
        (by
          unfold nb093_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r)
        (TAlphaVar.here _ _ _))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb093_split_alpha_0006 A r d dv_d_r)))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                          (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
                      ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide))
                  (freshVar_injective (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪
                      ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_136 A) from (by
                              unfold nb093_alpha_dummy_136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0138 A) 0))))
                          (show (nb093_alpha_dummy_047 r d) ≠ (nb093_alpha_dummy_138 r d) from
                            (by
                              unfold nb093_alpha_dummy_138;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0139 r d) 0))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_137 A) from (by
                                unfold nb093_alpha_dummy_137;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0138 A) 1)))) (show
                              (nb093_alpha_dummy_047 r d) ≠ (nb093_alpha_dummy_139 r d) from (by
                                unfold nb093_alpha_dummy_139;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0139 r d) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093_alpha_dummy_045 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb093_alpha_dummy_047 r d))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_143 A) from (by
          unfold nb093_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A) 1)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_146 r d) from (by
          unfold nb093_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_142 A) from (by
          unfold nb093_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_145 r d) from (by
          unfold nb093_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A),
        (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A),
        (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r
        d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from
                                      (by
                                        unfold nb093_alpha_dummy_140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0140 A)
                                                0)))) (show (nb093_alpha_dummy_138 r d) ≠
                                        (nb093_alpha_dummy_141 r d) from (by
                                        unfold nb093_alpha_dummy_141;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0141 r d) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)),
                                    ((nb093_alpha_dummy_136 A), (nb093_alpha_dummy_138 r d)),
                                    ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
                                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                    ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                    ((nb093_alpha_dummy_000 A), d),
                                    ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
                                      (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
                                      (nb093_alpha_dummy_005 A r d)),
                                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from
                                    (by
                                      unfold nb093_alpha_dummy_140;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0140 A)
                                              0)))) (show (nb093_alpha_dummy_138 r d) ≠
                                      (nb093_alpha_dummy_141 r d) from (by
                                      unfold nb093_alpha_dummy_141;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0141 r d)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from
                                      (by
                                        unfold nb093_alpha_dummy_140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0140 A)
                                                0)))) (show (nb093_alpha_dummy_138 r d) ≠
                                        (nb093_alpha_dummy_141 r d) from (by
                                        unfold nb093_alpha_dummy_141;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0141 r d) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)),
                                    ((nb093_alpha_dummy_136 A), (nb093_alpha_dummy_138 r d)),
                                    ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
                                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                    ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                    ((nb093_alpha_dummy_000 A), d),
                                    ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
                                      (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
                                      (nb093_alpha_dummy_005 A r d)),
                                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_054 A) from
                                      (by
                                        unfold nb093_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0050 A)
                                                0)))) (show r ≠ (nb093_alpha_dummy_055 r) from
                                      (by
                                        unfold nb093_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0051 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_052 A)
                                        from (by
                                          unfold nb093_alpha_dummy_052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0048 A) 0))))
                                      (show r ≠ (nb093_alpha_dummy_053 r) from (by
                                          unfold nb093_alpha_dummy_053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0049 r) 0))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_045 A) from (by
          unfold nb093_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 1)))) (show r ≠ (nb093_alpha_dummy_047 r d) from
        (by
          unfold nb093_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093_alpha_dummy_046 r d) from
        (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_050 A) from (by
          unfold nb093_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093_alpha_dummy_051 r d) from
        (by
          unfold nb093_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_048 A) from (by
          unfold nb093_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093_alpha_dummy_049 r d) from
        (by
          unfold nb093_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
        (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb093_split_alpha_0006 A r d dv_d_r)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_054 A) from
                                      (by
                                        unfold nb093_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0050 A)
                                                0)))) (show r ≠ (nb093_alpha_dummy_055 r) from
                                      (by
                                        unfold nb093_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0051 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_052 A)
                                        from (by
                                          unfold nb093_alpha_dummy_052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0048 A) 0))))
                                      (show r ≠ (nb093_alpha_dummy_053 r) from (by
                                          unfold nb093_alpha_dummy_053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0049 r) 0))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_045 A) from (by
          unfold nb093_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 1)))) (show r ≠ (nb093_alpha_dummy_047 r d) from
        (by
          unfold nb093_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093_alpha_dummy_046 r d) from
        (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_050 A) from (by
          unfold nb093_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093_alpha_dummy_051 r d) from
        (by
          unfold nb093_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_048 A) from (by
          unfold nb093_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093_alpha_dummy_049 r d) from
        (by
          unfold nb093_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
        (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb093_split_alpha_0006 A r d dv_d_r)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
                        ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide))
                    (freshVar_injective (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪
                        ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_136 A) from (by
                                unfold nb093_alpha_dummy_136;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0138 A) 0)))) (show
                              (nb093_alpha_dummy_047 r d) ≠ (nb093_alpha_dummy_138 r d) from (by
                                unfold nb093_alpha_dummy_138;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0139 r d) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_137 A) from
                                (by
                                  unfold nb093_alpha_dummy_137;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0138 A) 1)))) (show
                                (nb093_alpha_dummy_047 r d) ≠ (nb093_alpha_dummy_139 r d) from
                                (by
                                  unfold nb093_alpha_dummy_139;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0139 r d)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_045 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_047 r d))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_143 A) from (by
          unfold nb093_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A) 1)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_146 r d) from (by
          unfold nb093_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_142 A) from (by
          unfold nb093_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_145 r d) from (by
          unfold nb093_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A),
        (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A),
        (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_143
        A) ≠ (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A)
                                        from (by
                                          unfold nb093_alpha_dummy_140;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0140 A) 0)))) (show
                                        (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
                                          unfold nb093_alpha_dummy_141;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0141 r d) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)),
                                      ((nb093_alpha_dummy_136 A), (nb093_alpha_dummy_138 r d)),
                                      ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
                                      ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                      ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                      ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                      ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                      ((nb093_alpha_dummy_000 A), d),
                                      ((nb093_alpha_dummy_001 A), r),
                                      ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                                      ((nb093_alpha_dummy_004 A),
                                        (nb093_alpha_dummy_005 A r d)),
                                      ((nb093_alpha_dummy_002 A),
                                        (nb093_alpha_dummy_003 A r d))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from
                                      (by
                                        unfold nb093_alpha_dummy_140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0140 A)
                                                0)))) (show (nb093_alpha_dummy_138 r d) ≠
                                        (nb093_alpha_dummy_141 r d) from (by
                                        unfold nb093_alpha_dummy_141;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0141 r d) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A)
                                        from (by
                                          unfold nb093_alpha_dummy_140;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0140 A) 0)))) (show
                                        (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
                                          unfold nb093_alpha_dummy_141;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0141 r d) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)),
                                      ((nb093_alpha_dummy_136 A), (nb093_alpha_dummy_138 r d)),
                                      ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
                                      ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                      ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                      ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                      ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                      ((nb093_alpha_dummy_000 A), d),
                                      ((nb093_alpha_dummy_001 A), r),
                                      ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                                      ((nb093_alpha_dummy_004 A),
                                        (nb093_alpha_dummy_005 A r d)),
                                      ((nb093_alpha_dummy_002 A),
                                        (nb093_alpha_dummy_003 A r d))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb093_split_alpha_0008 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_158 A), (nb093_alpha_dummy_159 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_045 A))
          (Class.cv (nb093_alpha_dummy_000 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
            (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_047 r d)) (Class.cv d)) (Wff.neg
          (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
            (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_045 A) from (by
              unfold nb093_alpha_dummy_045;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))))
          (show d ≠ (nb093_alpha_dummy_047 r d) from (by
              unfold nb093_alpha_dummy_047;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))))
          (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_044 A) from (by
                unfold nb093_alpha_dummy_044;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))))
            (show d ≠ (nb093_alpha_dummy_046 r d) from (by
                unfold nb093_alpha_dummy_046;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))))
            (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_158 A) from
                (by
                  unfold nb093_alpha_dummy_158;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0164 A) 0))))
              (show d ≠ (nb093_alpha_dummy_159 r d) from (by
                  unfold nb093_alpha_dummy_159;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0165 r d) 0))))
              (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_048 A) from
                  (by
                    unfold nb093_alpha_dummy_048;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0161 A) 0))))
                (show d ≠ (nb093_alpha_dummy_049 r d) from (by
                    unfold nb093_alpha_dummy_049;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0163 r d) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                    (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
                ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide)) (freshVar_injective
              (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv)
              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_136 A) from
                                      (by
                                        unfold nb093_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0138 A)
                                                0)))) (show (nb093_alpha_dummy_047 r d) ≠
                                        (nb093_alpha_dummy_138 r d) from (by
                                        unfold nb093_alpha_dummy_138;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0139 r d) 0))))
                                    (TAlphaVar.there (show (nb093_alpha_dummy_045 A) ≠
        (nb093_alpha_dummy_137 A) from (by
                                          unfold nb093_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0138 A) 1)))) (show
                                        (nb093_alpha_dummy_047 r d) ≠
        (nb093_alpha_dummy_139 r d) from (by
                                          unfold nb093_alpha_dummy_139;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0139 r d) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_045 A) ≠
        (nb093_alpha_dummy_162 A) from (by
          unfold nb093_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0168 A) 0)))) (show (nb093_alpha_dummy_047 r d) ≠
        (nb093_alpha_dummy_163 r d) from (by
          unfold nb093_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0169 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_160 A) from (by
          unfold nb093_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0166 A) 0)))) (show (nb093_alpha_dummy_047 r d) ≠
        (nb093_alpha_dummy_161 r d) from (by
          unfold nb093_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0167 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_045 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_047 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_143 A) from (by
          unfold nb093_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  1)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_146 r d) from (by
          unfold nb093_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_142 A) from (by
          unfold nb093_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_145 r d) from (by
          unfold nb093_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_140 A) from (by
          unfold
            nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140
                    A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_141 r d) from (by
          unfold
            nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138
        r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_143
        A) ≠ (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_136 A) from
                                      (by
                                        unfold nb093_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0138 A)
                                                0)))) (show (nb093_alpha_dummy_047 r d) ≠
                                        (nb093_alpha_dummy_138 r d) from (by
                                        unfold nb093_alpha_dummy_138;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0139 r d) 0))))
                                    (TAlphaVar.there (show (nb093_alpha_dummy_045 A) ≠
        (nb093_alpha_dummy_137 A) from (by
                                          unfold nb093_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0138 A) 1)))) (show
                                        (nb093_alpha_dummy_047 r d) ≠
        (nb093_alpha_dummy_139 r d) from (by
                                          unfold nb093_alpha_dummy_139;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0139 r d) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_045 A) ≠
        (nb093_alpha_dummy_162 A) from (by
          unfold nb093_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0168 A) 0)))) (show (nb093_alpha_dummy_047 r d) ≠
        (nb093_alpha_dummy_163 r d) from (by
          unfold nb093_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0169 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_045 A) ≠ (nb093_alpha_dummy_160 A) from (by
          unfold nb093_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0166 A) 0)))) (show (nb093_alpha_dummy_047 r d) ≠
        (nb093_alpha_dummy_161 r d) from (by
          unfold nb093_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0167 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_045 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_047 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_143 A) from (by
          unfold nb093_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  1)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_146 r d) from (by
          unfold nb093_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_142 A) from (by
          unfold nb093_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_145 r d) from (by
          unfold nb093_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_140 A) from (by
          unfold
            nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140
                    A)
                  0)))) (show (nb093_alpha_dummy_138 r d) ≠ (nb093_alpha_dummy_141 r d) from (by
          unfold
            nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_150 A) from (by
          unfold
            nb093_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_151 r d) from (by
          unfold
            nb093_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_148 A) from (by
          unfold
            nb093_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_149 r d) from (by
          unfold
            nb093_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_144 A), (nb093_alpha_dummy_147 r d)), ((nb093_alpha_dummy_143 A),
        (nb093_alpha_dummy_146 r d)), ((nb093_alpha_dummy_142 A), (nb093_alpha_dummy_145 r d)),
        ((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138
        r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_143
        A) ≠ (nb093_alpha_dummy_154 A) from (by
          unfold
            nb093_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_155 r d) from (by
          unfold
            nb093_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_143 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093_alpha_dummy_146 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_136
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_144
        A) ≠ (nb093_alpha_dummy_156 A) from (by
          unfold
            nb093_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_157 r d) from (by
          unfold
            nb093_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_144 A) ≠
        (nb093_alpha_dummy_152 A) from (by
          unfold
            nb093_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093_alpha_dummy_147 r d) ≠ (nb093_alpha_dummy_153 r d) from (by
          unfold
            nb093_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠
        (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093_alpha_dummy_136 A) ≠ (nb093_alpha_dummy_140 A) from (by
          unfold nb093_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093_alpha_dummy_138 r d) ≠
        (nb093_alpha_dummy_141 r d) from (by
          unfold nb093_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_140 A), (nb093_alpha_dummy_141 r d)), ((nb093_alpha_dummy_136 A),
        (nb093_alpha_dummy_138 r d)), ((nb093_alpha_dummy_137 A), (nb093_alpha_dummy_139 r d)),
        ((nb093_alpha_dummy_162 A), (nb093_alpha_dummy_163 r d)), ((nb093_alpha_dummy_160 A),
        (nb093_alpha_dummy_161 r d)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_158 A),
        (nb093_alpha_dummy_159 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb093_alpha_dummy_160 A), (nb093_alpha_dummy_161 r d)),
                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                    ((nb093_alpha_dummy_158 A), (nb093_alpha_dummy_159 r d)),
                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                    ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                    ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                    ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb093_wpp_notmem_0422 (A : Class) :
    (nb093_alpha_dummy_000 A) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_000, fv_syn_cfound] using (nb093_compact_fv_empty_0020 A)

theorem nb093_wpp_notmem_0423 (d : Var) : d ∉ ((syn_cfound)).fv := by
  simpa only [fv_syn_cfound] using (nb093_compact_fv_empty_0021 d)

theorem nb093_wpp_notmem_0424 (A : Class) :
    (nb093_alpha_dummy_001 A) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_001, fv_syn_cfound] using (nb093_compact_fv_empty_0022 A)

theorem nb093_wpp_notmem_0425 (r : Var) : r ∉ ((syn_cfound)).fv := by
  simpa only [fv_syn_cfound] using (nb093_compact_fv_empty_0023 r)

theorem nb093_wpp_notmem_0426 (A : Class) :
    (nb093_alpha_dummy_006 A) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_006, fv_syn_cfound] using (nb093_compact_fv_empty_0024 A)

theorem nb093_wpp_notmem_0427 (r : Var) (d : Var) :
    (nb093_alpha_dummy_007 r d) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_007, fv_syn_cfound] using
    (nb093_compact_fv_empty_0025 r d)

theorem nb093_wpp_notmem_0428 (A : Class) :
    (nb093_alpha_dummy_004 A) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_cfound] using (nb093_compact_fv_empty_0026 A)

theorem nb093_wpp_notmem_0429 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_005 A r d) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_cfound] using
    (nb093_compact_fv_empty_0027 A r d)

theorem nb093_wpp_notmem_0430 (A : Class) :
    (nb093_alpha_dummy_002 A) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_cfound] using (nb093_compact_fv_empty_0028 A)

theorem nb093_wpp_notmem_0431 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_003 A r d) ∉ ((syn_cfound)).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_cfound] using
    (nb093_compact_fv_empty_0029 A r d)

theorem nb093_compact_envfresh_0029 (A : Class) (r : Var) (d : Var) :
    TEnvFresh
      [((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      ((syn_cfound)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb093_alpha_dummy_000 A) d (nb093_wpp_notmem_0422 A)
      (nb093_wpp_notmem_0423 d)
      (TEnvFresh.consFresh (nb093_alpha_dummy_001 A) r (nb093_wpp_notmem_0424 A)
        (nb093_wpp_notmem_0425 r)
        (TEnvFresh.consFresh (nb093_alpha_dummy_006 A) (nb093_alpha_dummy_007 r d)
          (nb093_wpp_notmem_0426 A) (nb093_wpp_notmem_0427 r d)
          (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d)
            (nb093_wpp_notmem_0428 A) (nb093_wpp_notmem_0429 A r d)
            (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d)
              (nb093_wpp_notmem_0430 A) (nb093_wpp_notmem_0431 A r d)
              (TEnvFresh.nil ((syn_cfound)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
