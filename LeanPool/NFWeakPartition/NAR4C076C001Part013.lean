/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C076C001Part013Stage1


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
noncomputable def nb076_wpp_refl_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TReflOn
      [((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      ((syn_cen)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0029 g m n a b)

@[expose]
noncomputable def nominal_df_muc (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) (dv_a_m : a ≠ m) (dv_a_n : a ≠ n) (dv_b_g : b ≠ g)
    (dv_b_m : b ≠ m) (dv_b_n : b ≠ n) (__dv_g_m : g ≠ m) (dv_g_n : g ≠ n)
    (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classEq (syn_cmuc) (syn_cmpt2 m (syn_cncs) n (syn_cncs) (.cab a (syn_wrex b (.cv m)
              (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_007) from (by
                            unfold nb076_alpha_dummy_007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0004) 0))))) (Ne.symm
                        (show (nb076_alpha_dummy_006 g m n a b) ≠
                            (nb076_alpha_dummy_008 g m n a b) from (by
                            unfold nb076_alpha_dummy_008;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0005 g m n a b)
                                    0))))) (TAlphaVar.there (Ne.symm
                          (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_007) from (by
                              unfold nb076_alpha_dummy_007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0002) 0))))) (Ne.symm
                          (show n ≠ (nb076_alpha_dummy_008 g m n a b) from (by
                              unfold nb076_alpha_dummy_008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0003 g m n a b)
                                      0))))) (TAlphaVar.there (Ne.symm
                            (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_007) from (by
                                unfold nb076_alpha_dummy_007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0000) 0))))) (Ne.symm
                            (show m ≠ (nb076_alpha_dummy_008 g m n a b) from (by
                                unfold nb076_alpha_dummy_008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0001 g m n a b)
                                        0))))) (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb076_split_alpha_0002 g m n a b dv_m_n)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb076_split_alpha_0003 g m n a b)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb076_split_alpha_0003 g m n a b)))))))))))))
                (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_005) from (by
                              unfold nb076_alpha_dummy_005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0006) 0))))
                          (show m ≠ (nb076_alpha_dummy_006 g m n a b) from (by
                              unfold nb076_alpha_dummy_006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0007 g m n a b)
                                      0)))) (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_m_n
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.refl_of_reflOn
                        [((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
                          ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                          ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                        (syn_cncs) (nb076_wpp_refl_0014 g m n a b))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_005) from (by
                              unfold nb076_alpha_dummy_005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0042) 0))))
                          (show n ≠ (nb076_alpha_dummy_006 g m n a b) from (by
                              unfold nb076_alpha_dummy_006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0043 g m n a b)
                                      0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
                        [((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
                          ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                          ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                        (syn_cncs) (nb076_wpp_refl_0014 g m n a b))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_b_m) (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  (Ne.symm dv_a_m) (TAlphaVar.there (show
                                      (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_005) from (by
                                        unfold nb076_alpha_dummy_005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0006)
                                                0))))
                                    (show m ≠ (nb076_alpha_dummy_006 g m n a b) from (by
                                        unfold nb076_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0007 g m n a b) 0))))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_m_n (TAlphaVar.here _ _ _))))))) (TAlphaWff.ex
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    (Ne.symm dv_g_n) (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      (Ne.symm dv_b_n) (TAlphaVar.there
                                        (freshVar_injective ((∅ : Finset Var)) (by decide))
                                        (Ne.symm dv_a_n) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_005) from (by
          unfold nb076_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042) 0))))
        (show n ≠ (nb076_alpha_dummy_006 g m n a b) from (by
          unfold nb076_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043 g m n a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0004 g m n a b dv_a_b dv_a_g)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (Ne.symm (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_117) from
        (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0122)
                  0))))) (Ne.symm (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_118
        g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0123
                    g b)
                  0))))) (TAlphaVar.there (Ne.symm (show (nb076_alpha_dummy_113) ≠
        (nb076_alpha_dummy_117) from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0120)
                  0))))) (Ne.symm (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_118
        g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0121
                    g
                    b)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0005 g m n a b)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠
        (nb076_alpha_dummy_120) from (by
          unfold
            nb076_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
          unfold
            nb076_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_119)
        from (by
          unfold
            nb076_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold
            nb076_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_149)
        from (by
          unfold
            nb076_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_150 g b) from (by
          unfold
            nb076_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_123)
        from (by
          unfold
            nb076_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_124 g b) from (by
          unfold
            nb076_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_113))).fv ∪
        ((Class.cv (nb076_alpha_dummy_114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv
        (nb076_alpha_dummy_116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)), ((nb076_alpha_dummy_120),
        (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)), ((nb076_alpha_dummy_123),
        (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117),
        (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a
        b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a
        b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠
        (nb076_alpha_dummy_120) from (by
          unfold
            nb076_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
          unfold
            nb076_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_119)
        from (by
          unfold
            nb076_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold
            nb076_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_149)
        from (by
          unfold
            nb076_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_150 g b) from (by
          unfold
            nb076_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_123)
        from (by
          unfold
            nb076_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_124 g b) from (by
          unfold
            nb076_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_113))).fv ∪
        ((Class.cv (nb076_alpha_dummy_114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv
        (nb076_alpha_dummy_116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)), ((nb076_alpha_dummy_120),
        (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)), ((nb076_alpha_dummy_123),
        (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117),
        (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a
        b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a
        b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_001))).fv ∪
        ((Class.cv (nb076_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv
        b)).fv ∪ ((Class.cv g)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_114) from (by
          unfold
            nb076_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  1)))) (show b ≠ (nb076_alpha_dummy_116 g b) from (by
          unfold
            nb076_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_113)
        from (by
          unfold
            nb076_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  0)))) (show b ≠ (nb076_alpha_dummy_115 g b) from (by
          unfold
            nb076_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_117)
        from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0168)
                  0)))) (show b ≠ (nb076_alpha_dummy_118 g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0169
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_082)
        from (by
          unfold
            nb076_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  1)))) (show b ≠ (nb076_alpha_dummy_084 g a b) from (by
          unfold
            nb076_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_081)
        from (by
          unfold
            nb076_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  0)))) (show b ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold
            nb076_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_111)
        from (by
          unfold
            nb076_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0166)
                  0)))) (show b ≠ (nb076_alpha_dummy_112 g a b) from (by
          unfold
            nb076_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0167
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_085)
        from (by
          unfold
            nb076_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0163)
                  0)))) (show b ≠ (nb076_alpha_dummy_086 g a b) from (by
          unfold
            nb076_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0165
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by
          decide)) dv_b_g (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠
        (nb076_alpha_dummy_114) from (by
          unfold
            nb076_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  1)))) (show g ≠ (nb076_alpha_dummy_116 g b) from (by
          unfold
            nb076_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_113)
        from (by
          unfold
            nb076_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  0)))) (show g ≠ (nb076_alpha_dummy_115 g b) from (by
          unfold
            nb076_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_117)
        from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0178)
                  0)))) (show g ≠ (nb076_alpha_dummy_118 g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0179
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_082)
        from (by
          unfold
            nb076_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  1)))) (show g ≠ (nb076_alpha_dummy_084 g a b) from (by
          unfold
            nb076_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_081)
        from (by
          unfold
            nb076_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  0)))) (show g ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold
            nb076_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_111)
        from (by
          unfold
            nb076_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0176)
                  0)))) (show g ≠ (nb076_alpha_dummy_112 g a b) from (by
          unfold
            nb076_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0177
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_085)
        from (by
          unfold
            nb076_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0173)
                  0)))) (show g ≠ (nb076_alpha_dummy_086 g a b) from (by
          unfold
            nb076_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0175
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))) (nb076_split_alpha_0007 g m n a
        b))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
        (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_117) from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0122)
                  0))))) (Ne.symm (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_118
        g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0123
                    g b)
                  0))))) (TAlphaVar.there (Ne.symm (show (nb076_alpha_dummy_113) ≠
        (nb076_alpha_dummy_117) from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0120)
                  0))))) (Ne.symm (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_118
        g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0121
                    g
                    b)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0005 g m n a b)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠
        (nb076_alpha_dummy_120) from (by
          unfold
            nb076_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
          unfold
            nb076_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_119)
        from (by
          unfold
            nb076_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold
            nb076_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_149)
        from (by
          unfold
            nb076_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_150 g b) from (by
          unfold
            nb076_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_123)
        from (by
          unfold
            nb076_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_124 g b) from (by
          unfold
            nb076_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_113))).fv ∪
        ((Class.cv (nb076_alpha_dummy_114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv
        (nb076_alpha_dummy_116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)), ((nb076_alpha_dummy_120),
        (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)), ((nb076_alpha_dummy_123),
        (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117),
        (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a
        b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a
        b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠
        (nb076_alpha_dummy_120) from (by
          unfold
            nb076_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
          unfold
            nb076_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_119)
        from (by
          unfold
            nb076_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold
            nb076_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_149)
        from (by
          unfold
            nb076_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_150 g b) from (by
          unfold
            nb076_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_123)
        from (by
          unfold
            nb076_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_124 g b) from (by
          unfold
            nb076_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_113))).fv ∪
        ((Class.cv (nb076_alpha_dummy_114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv
        (nb076_alpha_dummy_116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076_split_alpha_0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_151), (nb076_alpha_dummy_152 g b)), ((nb076_alpha_dummy_120),
        (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)),
        ((nb076_alpha_dummy_149), (nb076_alpha_dummy_150 g b)), ((nb076_alpha_dummy_123),
        (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)),
        ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117),
        (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)),
        ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111),
        (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a
        b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b),
        ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a
        b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_001))).fv ∪
        ((Class.cv (nb076_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv
        b)).fv ∪ ((Class.cv g)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_114) from (by
          unfold
            nb076_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  1)))) (show b ≠ (nb076_alpha_dummy_116 g b) from (by
          unfold
            nb076_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_113)
        from (by
          unfold
            nb076_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  0)))) (show b ≠ (nb076_alpha_dummy_115 g b) from (by
          unfold
            nb076_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_117)
        from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0168)
                  0)))) (show b ≠ (nb076_alpha_dummy_118 g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0169
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_082)
        from (by
          unfold
            nb076_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  1)))) (show b ≠ (nb076_alpha_dummy_084 g a b) from (by
          unfold
            nb076_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_081)
        from (by
          unfold
            nb076_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  0)))) (show b ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold
            nb076_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_111)
        from (by
          unfold
            nb076_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0166)
                  0)))) (show b ≠ (nb076_alpha_dummy_112 g a b) from (by
          unfold
            nb076_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0167
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_085)
        from (by
          unfold
            nb076_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0163)
                  0)))) (show b ≠ (nb076_alpha_dummy_086 g a b) from (by
          unfold
            nb076_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0165
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by
          decide)) dv_b_g (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠
        (nb076_alpha_dummy_114) from (by
          unfold
            nb076_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  1)))) (show g ≠ (nb076_alpha_dummy_116 g b) from (by
          unfold
            nb076_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_113)
        from (by
          unfold
            nb076_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  0)))) (show g ≠ (nb076_alpha_dummy_115 g b) from (by
          unfold
            nb076_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_117)
        from (by
          unfold
            nb076_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0178)
                  0)))) (show g ≠ (nb076_alpha_dummy_118 g b) from (by
          unfold
            nb076_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0179
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_082)
        from (by
          unfold
            nb076_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  1)))) (show g ≠ (nb076_alpha_dummy_084 g a b) from (by
          unfold
            nb076_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_081)
        from (by
          unfold
            nb076_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  0)))) (show g ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold
            nb076_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_111)
        from (by
          unfold
            nb076_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0176)
                  0)))) (show g ≠ (nb076_alpha_dummy_112 g a b) from (by
          unfold
            nb076_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0177
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_085)
        from (by
          unfold
            nb076_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0173)
                  0)))) (show g ≠ (nb076_alpha_dummy_086 g a b) from (by
          unfold
            nb076_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0175
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))) (nb076_split_alpha_0007 g m n a
        b)))))))))))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_002), g),
                                    ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cen) (nb076_wpp_refl_0029 g m n a b)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
