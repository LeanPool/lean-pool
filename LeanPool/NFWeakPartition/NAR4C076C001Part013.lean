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

/-- Checked nominal proof certificate identified upstream as `nb076_wpp_refl_0029`. -/
@[expose]
noncomputable def nb076WppRefl0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TReflOn
      [((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      ((synCen)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0029 g m n a b)

/-- Checked nominal proof certificate identified upstream as `nominal_df_muc`. -/
@[expose]
noncomputable def nominalDfMuc (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) (dv_a_m : a ≠ m) (dv_a_n : a ≠ n) (dv_b_g : b ≠ g)
    (dv_b_m : b ≠ m) (dv_b_n : b ≠ n) (__dv_g_m : g ≠ m) (dv_g_n : g ≠ n)
    (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classEq (synCmuc) (synCmpt2 m (synCncs) n (synCncs) (.cab a (synWrex b (.cv m)
              (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy007) from (by
                            unfold nb076AlphaDummy007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0004) 0))))) (Ne.symm
                        (show (nb076AlphaDummy006 g m n a b) ≠
                            (nb076AlphaDummy008 g m n a b) from (by
                            unfold nb076AlphaDummy008;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0005 g m n a b)
                                    0))))) (TAlphaVar.there (Ne.symm
                          (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy007) from (by
                              unfold nb076AlphaDummy007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0002) 0))))) (Ne.symm
                          (show n ≠ (nb076AlphaDummy008 g m n a b) from (by
                              unfold nb076AlphaDummy008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0003 g m n a b)
                                      0))))) (TAlphaVar.there (Ne.symm
                            (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy007) from (by
                                unfold nb076AlphaDummy007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0000) 0))))) (Ne.symm
                            (show m ≠ (nb076AlphaDummy008 g m n a b) from (by
                                unfold nb076AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0001 g m n a b)
                                        0))))) (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb076SplitAlpha0002 g m n a b dv_m_n)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb076SplitAlpha0003 g m n a b)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb076SplitAlpha0003 g m n a b)))))))))))))
                (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy003) ≠ (nb076AlphaDummy005) from (by
                              unfold nb076AlphaDummy005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0006) 0))))
                          (show m ≠ (nb076AlphaDummy006 g m n a b) from (by
                              unfold nb076AlphaDummy006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0007 g m n a b)
                                      0)))) (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_m_n
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.reflOfReflOn
                        [((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
                          ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                          ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                        (synCncs) (nb076WppRefl0014 g m n a b))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy005) from (by
                              unfold nb076AlphaDummy005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0042) 0))))
                          (show n ≠ (nb076AlphaDummy006 g m n a b) from (by
                              unfold nb076AlphaDummy006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0043 g m n a b)
                                      0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
                        [((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
                          ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                          ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                        (synCncs) (nb076WppRefl0014 g m n a b))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_b_m) (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  (Ne.symm dv_a_m) (TAlphaVar.there (show
                                      (nb076AlphaDummy003) ≠ (nb076AlphaDummy005) from (by
                                        unfold nb076AlphaDummy005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0006)
                                                0))))
                                    (show m ≠ (nb076AlphaDummy006 g m n a b) from (by
                                        unfold nb076AlphaDummy006;
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
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy005) from (by
          unfold nb076AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042) 0))))
        (show n ≠ (nb076AlphaDummy006 g m n a b) from (by
          unfold nb076AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043 g m n a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0004 g m n a b dv_a_b dv_a_g)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (Ne.symm (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy117) from
        (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0122)
                  0))))) (Ne.symm (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy118
        g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0123
                    g b)
                  0))))) (TAlphaVar.there (Ne.symm (show (nb076AlphaDummy113) ≠
        (nb076AlphaDummy117) from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0120)
                  0))))) (Ne.symm (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy118
        g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0121
                    g
                    b)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0005 g m n a b)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy114) ≠
        (nb076AlphaDummy120) from (by
          unfold
            nb076AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy122 g b) from (by
          unfold
            nb076AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy119)
        from (by
          unfold
            nb076AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold
            nb076AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy149)
        from (by
          unfold
            nb076AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy150 g b) from (by
          unfold
            nb076AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy123)
        from (by
          unfold
            nb076AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy124 g b) from (by
          unfold
            nb076AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy113))).fv ∪
        ((Class.cv (nb076AlphaDummy114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy115 g b))).fv ∪ ((Class.cv
        (nb076AlphaDummy116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy151), (nb076AlphaDummy152 g b)), ((nb076AlphaDummy120),
        (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)), ((nb076AlphaDummy123),
        (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)), ((nb076AlphaDummy117),
        (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085), (nb076AlphaDummy086 g a
        b)), ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a), ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a
        b)), ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy114) ≠
        (nb076AlphaDummy120) from (by
          unfold
            nb076AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy122 g b) from (by
          unfold
            nb076AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy119)
        from (by
          unfold
            nb076AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold
            nb076AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy149)
        from (by
          unfold
            nb076AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy150 g b) from (by
          unfold
            nb076AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy123)
        from (by
          unfold
            nb076AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy124 g b) from (by
          unfold
            nb076AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy113))).fv ∪
        ((Class.cv (nb076AlphaDummy114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy115 g b))).fv ∪ ((Class.cv
        (nb076AlphaDummy116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy151), (nb076AlphaDummy152 g b)), ((nb076AlphaDummy120),
        (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)), ((nb076AlphaDummy123),
        (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)), ((nb076AlphaDummy117),
        (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085), (nb076AlphaDummy086 g a
        b)), ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a), ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a
        b)), ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy001))).fv ∪
        ((Class.cv (nb076AlphaDummy002))).fv) (by decide)) (freshVar_injective (((Class.cv
        b)).fv ∪ ((Class.cv g)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy114) from (by
          unfold
            nb076AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  1)))) (show b ≠ (nb076AlphaDummy116 g b) from (by
          unfold
            nb076AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy113)
        from (by
          unfold
            nb076AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  0)))) (show b ≠ (nb076AlphaDummy115 g b) from (by
          unfold
            nb076AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy117)
        from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0168)
                  0)))) (show b ≠ (nb076AlphaDummy118 g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0169
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy082)
        from (by
          unfold
            nb076AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  1)))) (show b ≠ (nb076AlphaDummy084 g a b) from (by
          unfold
            nb076AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy081)
        from (by
          unfold
            nb076AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  0)))) (show b ≠ (nb076AlphaDummy083 g a b) from (by
          unfold
            nb076AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy111)
        from (by
          unfold
            nb076AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0166)
                  0)))) (show b ≠ (nb076AlphaDummy112 g a b) from (by
          unfold
            nb076AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0167
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy085)
        from (by
          unfold
            nb076AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0163)
                  0)))) (show b ≠ (nb076AlphaDummy086 g a b) from (by
          unfold
            nb076AlphaDummy086;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy002) ≠
        (nb076AlphaDummy114) from (by
          unfold
            nb076AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  1)))) (show g ≠ (nb076AlphaDummy116 g b) from (by
          unfold
            nb076AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy113)
        from (by
          unfold
            nb076AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  0)))) (show g ≠ (nb076AlphaDummy115 g b) from (by
          unfold
            nb076AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy117)
        from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0178)
                  0)))) (show g ≠ (nb076AlphaDummy118 g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0179
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy082)
        from (by
          unfold
            nb076AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  1)))) (show g ≠ (nb076AlphaDummy084 g a b) from (by
          unfold
            nb076AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy081)
        from (by
          unfold
            nb076AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  0)))) (show g ≠ (nb076AlphaDummy083 g a b) from (by
          unfold
            nb076AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy111)
        from (by
          unfold
            nb076AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0176)
                  0)))) (show g ≠ (nb076AlphaDummy112 g a b) from (by
          unfold
            nb076AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0177
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy085)
        from (by
          unfold
            nb076AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0173)
                  0)))) (show g ≠ (nb076AlphaDummy086 g a b) from (by
          unfold
            nb076AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0175
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))) (nb076SplitAlpha0007 g m n a
        b))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
        (nb076AlphaDummy114) ≠ (nb076AlphaDummy117) from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0122)
                  0))))) (Ne.symm (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy118
        g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0123
                    g b)
                  0))))) (TAlphaVar.there (Ne.symm (show (nb076AlphaDummy113) ≠
        (nb076AlphaDummy117) from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0120)
                  0))))) (Ne.symm (show (nb076AlphaDummy115 g b) ≠ (nb076AlphaDummy118
        g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0121
                    g
                    b)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0005 g m n a b)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy114) ≠
        (nb076AlphaDummy120) from (by
          unfold
            nb076AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy122 g b) from (by
          unfold
            nb076AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy119)
        from (by
          unfold
            nb076AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold
            nb076AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy149)
        from (by
          unfold
            nb076AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy150 g b) from (by
          unfold
            nb076AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy123)
        from (by
          unfold
            nb076AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy124 g b) from (by
          unfold
            nb076AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy113))).fv ∪
        ((Class.cv (nb076AlphaDummy114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy115 g b))).fv ∪ ((Class.cv
        (nb076AlphaDummy116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy151), (nb076AlphaDummy152 g b)), ((nb076AlphaDummy120),
        (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)), ((nb076AlphaDummy123),
        (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)), ((nb076AlphaDummy117),
        (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085), (nb076AlphaDummy086 g a
        b)), ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a), ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a
        b)), ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy114) ≠
        (nb076AlphaDummy120) from (by
          unfold
            nb076AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  1)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy122 g b) from (by
          unfold
            nb076AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy119)
        from (by
          unfold
            nb076AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0152)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy121 g b) from (by
          unfold
            nb076AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0154
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy149)
        from (by
          unfold
            nb076AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0156)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy150 g b) from (by
          unfold
            nb076AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0157
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy114) ≠ (nb076AlphaDummy123)
        from (by
          unfold
            nb076AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0153)
                  0)))) (show (nb076AlphaDummy116 g b) ≠ (nb076AlphaDummy124 g b) from (by
          unfold
            nb076AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0155
                    g
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy113))).fv ∪
        ((Class.cv (nb076AlphaDummy114))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy115 g b))).fv ∪ ((Class.cv
        (nb076AlphaDummy116 g b))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb076SplitAlpha0006 g m n a b))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy151), (nb076AlphaDummy152 g b)), ((nb076AlphaDummy120),
        (nb076AlphaDummy122 g b)), ((nb076AlphaDummy119), (nb076AlphaDummy121 g b)),
        ((nb076AlphaDummy149), (nb076AlphaDummy150 g b)), ((nb076AlphaDummy123),
        (nb076AlphaDummy124 g b)), ((nb076AlphaDummy114), (nb076AlphaDummy116 g b)),
        ((nb076AlphaDummy113), (nb076AlphaDummy115 g b)), ((nb076AlphaDummy117),
        (nb076AlphaDummy118 g b)), ((nb076AlphaDummy082), (nb076AlphaDummy084 g a b)),
        ((nb076AlphaDummy081), (nb076AlphaDummy083 g a b)), ((nb076AlphaDummy111),
        (nb076AlphaDummy112 g a b)), ((nb076AlphaDummy085), (nb076AlphaDummy086 g a
        b)), ((nb076AlphaDummy002), g), ((nb076AlphaDummy001), b),
        ((nb076AlphaDummy000), a), ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a
        b)), ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy001))).fv ∪
        ((Class.cv (nb076AlphaDummy002))).fv) (by decide)) (freshVar_injective (((Class.cv
        b)).fv ∪ ((Class.cv g)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy114) from (by
          unfold
            nb076AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  1)))) (show b ≠ (nb076AlphaDummy116 g b) from (by
          unfold
            nb076AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy113)
        from (by
          unfold
            nb076AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0170)
                  0)))) (show b ≠ (nb076AlphaDummy115 g b) from (by
          unfold
            nb076AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0171
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy117)
        from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0168)
                  0)))) (show b ≠ (nb076AlphaDummy118 g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0169
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy082)
        from (by
          unfold
            nb076AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  1)))) (show b ≠ (nb076AlphaDummy084 g a b) from (by
          unfold
            nb076AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy081)
        from (by
          unfold
            nb076AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0162)
                  0)))) (show b ≠ (nb076AlphaDummy083 g a b) from (by
          unfold
            nb076AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0164
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy111)
        from (by
          unfold
            nb076AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0166)
                  0)))) (show b ≠ (nb076AlphaDummy112 g a b) from (by
          unfold
            nb076AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0167
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy001) ≠ (nb076AlphaDummy085)
        from (by
          unfold
            nb076AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0163)
                  0)))) (show b ≠ (nb076AlphaDummy086 g a b) from (by
          unfold
            nb076AlphaDummy086;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy002) ≠
        (nb076AlphaDummy114) from (by
          unfold
            nb076AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  1)))) (show g ≠ (nb076AlphaDummy116 g b) from (by
          unfold
            nb076AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy113)
        from (by
          unfold
            nb076AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0180)
                  0)))) (show g ≠ (nb076AlphaDummy115 g b) from (by
          unfold
            nb076AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0181
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy117)
        from (by
          unfold
            nb076AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0178)
                  0)))) (show g ≠ (nb076AlphaDummy118 g b) from (by
          unfold
            nb076AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0179
                    g
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy082)
        from (by
          unfold
            nb076AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  1)))) (show g ≠ (nb076AlphaDummy084 g a b) from (by
          unfold
            nb076AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy081)
        from (by
          unfold
            nb076AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0172)
                  0)))) (show g ≠ (nb076AlphaDummy083 g a b) from (by
          unfold
            nb076AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0174
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy111)
        from (by
          unfold
            nb076AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0176)
                  0)))) (show g ≠ (nb076AlphaDummy112 g a b) from (by
          unfold
            nb076AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0177
                    g
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy085)
        from (by
          unfold
            nb076AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0173)
                  0)))) (show g ≠ (nb076AlphaDummy086 g a b) from (by
          unfold
            nb076AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0175
                    g
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))) (nb076SplitAlpha0007 g m n a
        b)))))))))))) (TAlphaClass.reflOfReflOn [((nb076AlphaDummy002), g),
                                    ((nb076AlphaDummy001), b), ((nb076AlphaDummy000), a),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCen) (nb076WppRefl0029 g m n a b)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
