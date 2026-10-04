/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part045

/-! NF weak partition development: NAR4H5C095M3Part046. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0102`. -/
@[expose]
noncomputable def nb095SplitAlpha0102 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (synWbr (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E))) (synCin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))
          (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E))))
        (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E)) (synCin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))
          (Class.cv (nb095AlphaDummy004 D R S_cls E))))
      (Wff.imp (synWbr
          (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
          (synCin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))
          (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))))
        (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))
          (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb095SplitAlpha0092 x u D R S_cls f E dv_f_u dv_f_x)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095SplitAlpha0095 x u D R S_cls f E dv_f_u dv_f_x)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095SplitAlpha0095 x u D R S_cls f E dv_f_u dv_f_x))))))))))))
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy791 D R S_cls E),
                            (nb095AlphaDummy792 u S_cls E)),
                          ((nb095AlphaDummy789 D R S_cls E),
                            (nb095AlphaDummy790 u S_cls E)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] S_cls
                        (nb095FocusedRefl0009 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
                                          unfold nb095AlphaDummy797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0844 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy796 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
                                          unfold nb095AlphaDummy798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0845 u S_cls E)
                                                  0))))) (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0842 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy795 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0843 u S_cls E)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0096 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0100 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x dv_S_f dv_S_u dv_S_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy791 D R S_cls E),
                            (nb095AlphaDummy792 u S_cls E)),
                          ((nb095AlphaDummy789 D R S_cls E),
                            (nb095AlphaDummy790 u S_cls E)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] S_cls
                        (nb095FocusedRefl0009 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
                                          unfold nb095AlphaDummy797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0844 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy796 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
                                          unfold nb095AlphaDummy798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0845 u S_cls E)
                                                  0))))) (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0842 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy795 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0843 u S_cls E)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0096 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0100 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x dv_S_f dv_S_u dv_S_x))))))))))))))) (TAlphaWff.classMem
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0083 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.neg (nb095SplitAlpha0084 x u D R S_cls f E)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095SplitAlpha0084 x u D R S_cls f E))))))))))))
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy617 D R S_cls E),
                            (nb095AlphaDummy618 x D R)),
                          ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] R
                        (nb095FocusedRefl0007 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
                                          unfold nb095AlphaDummy623;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0642 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy622 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
                                          unfold nb095AlphaDummy624;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0643 x D R) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0640 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy621 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0641 x D R) 0))))) (TAlphaVar.here _ _ _))))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0085 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0089 x u D R S_cls f E dv_D_f dv_D_u
                                  dv_D_x dv_R_f dv_R_u dv_R_x dv_u_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy617 D R S_cls E),
                            (nb095AlphaDummy618 x D R)),
                          ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] R
                        (nb095FocusedRefl0007 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
                                          unfold nb095AlphaDummy623;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0642 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy622 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
                                          unfold nb095AlphaDummy624;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0643 x D R) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0640 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy621 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0641 x D R) 0))))) (TAlphaVar.here _ _ _))))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0085 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0089 x u D R S_cls f E dv_D_f dv_D_u
                                  dv_D_x dv_R_f dv_R_u dv_R_x dv_u_x))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0103`. -/
@[expose]
noncomputable def nb095SplitAlpha0103 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy003 D R S_cls E)) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
        (synWral (nb095AlphaDummy004 D R S_cls E) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synWb
            (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E)) (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))
              (Class.cv (nb095AlphaDummy004 D R S_cls E))) (synWbr
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E))) (synCin S_cls (synCxp
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
        (synWral (nb095AlphaDummy006 x u D R S_cls f E)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
          (synWb (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))) (synWbr
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u)))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                            (nb095AlphaDummy248 x D R)),
                          ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] D
                        (nb095FocusedRefl0005 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy253 D R S_cls E) from (by
                                          unfold nb095AlphaDummy253;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0256 D R S_cls E)
                                                  0)))) (show x ≠ (nb095AlphaDummy254 x) from
                                        (by
                                          unfold nb095AlphaDummy254;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0257 x) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) from (by
          unfold nb095AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy252 x R) from (by
          unfold nb095AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy249 D R S_cls E) from (by
          unfold nb095AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy251 x R) from (by
          unfold nb095AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy247 D R S_cls E) from (by
          unfold nb095AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095AlphaDummy248 x D R) from (by
          unfold nb095AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy245 D R S_cls E) from (by
          unfold nb095AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy246 x D R) from (by
          unfold nb095AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0079 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0080 x u D R S_cls f E))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0080 x u D R S_cls f E)))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb095AlphaDummy250 D R S_cls E),
                                    (nb095AlphaDummy252 x R)),
                                  ((nb095AlphaDummy249 D R S_cls E),
                                    (nb095AlphaDummy251 x R)),
                                  ((nb095AlphaDummy247 D R S_cls E),
                                    (nb095AlphaDummy248 x D R)),
                                  ((nb095AlphaDummy245 D R S_cls E),
                                    (nb095AlphaDummy246 x D R)),
                                  ((nb095AlphaDummy003 D R S_cls E),
                                    (nb095AlphaDummy005 x u D R S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCcnv (synCdif R (synCid)))
                                (nb095WppRefl0267 x u D R S_cls f E dv_R_f dv_R_u
                                  dv_R_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                            (nb095AlphaDummy248 x D R)),
                          ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] D
                        (nb095FocusedRefl0005 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy253 D R S_cls E) from (by
                                          unfold nb095AlphaDummy253;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0256 D R S_cls E)
                                                  0)))) (show x ≠ (nb095AlphaDummy254 x) from
                                        (by
                                          unfold nb095AlphaDummy254;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0257 x) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) from (by
          unfold nb095AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy252 x R) from (by
          unfold nb095AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy249 D R S_cls E) from (by
          unfold nb095AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy251 x R) from (by
          unfold nb095AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy247 D R S_cls E) from (by
          unfold nb095AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095AlphaDummy248 x D R) from (by
          unfold nb095AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy245 D R S_cls E) from (by
          unfold nb095AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy246 x D R) from (by
          unfold nb095AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0079 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0080 x u D R S_cls f E))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0080 x u D R S_cls f E)))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb095AlphaDummy250 D R S_cls E),
                                    (nb095AlphaDummy252 x R)),
                                  ((nb095AlphaDummy249 D R S_cls E),
                                    (nb095AlphaDummy251 x R)),
                                  ((nb095AlphaDummy247 D R S_cls E),
                                    (nb095AlphaDummy248 x D R)),
                                  ((nb095AlphaDummy245 D R S_cls E),
                                    (nb095AlphaDummy246 x D R)),
                                  ((nb095AlphaDummy003 D R S_cls E),
                                    (nb095AlphaDummy005 x u D R S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCcnv (synCdif R (synCid)))
                                (nb095WppRefl0267 x u D R S_cls f E dv_R_f dv_R_u
                                  dv_R_x))))))))))))))) (TAlphaWff.all (TAlphaWff.imp
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                                (nb095AlphaDummy248 x D R)),
                              ((nb095AlphaDummy245 D R S_cls E),
                                (nb095AlphaDummy246 x D R)),
                              ((nb095AlphaDummy004 D R S_cls E),
                                (nb095AlphaDummy006 x u D R S_cls f E)),
                              ((nb095AlphaDummy003 D R S_cls E),
                                (nb095AlphaDummy005 x u D R S_cls f E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)] D
                            (nb095FocusedRefl0006 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy253 D R S_cls E) from (by
          unfold nb095AlphaDummy253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy254 x) from (by
          unfold nb095AlphaDummy254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) from (by
          unfold nb095AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  1)))) (show x ≠ (nb095AlphaDummy252 x R) from (by
          unfold nb095AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy249 D R S_cls E) from (by
          unfold nb095AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy251 x R) from (by
          unfold nb095AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy247 D R S_cls E) from (by
          unfold nb095AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy248 x D R) from (by
          unfold nb095AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy245 D R S_cls E) from (by
          unfold nb095AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy246 x D R) from (by
          unfold nb095AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D
                    R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600 D
                    R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601 x
                    u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _)))))))))))))
                                (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0081 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0082 x u D R S_cls f E)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0082 x u D R S_cls f E)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                    [((nb095AlphaDummy250 D R S_cls E),
                                        (nb095AlphaDummy252 x R)),
                                      ((nb095AlphaDummy249 D R S_cls E),
                                        (nb095AlphaDummy251 x R)),
                                      ((nb095AlphaDummy247 D R S_cls E),
                                        (nb095AlphaDummy248 x D R)),
                                      ((nb095AlphaDummy245 D R S_cls E),
                                        (nb095AlphaDummy246 x D R)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCcnv (synCdif R (synCid)))
                                    (nb095WppRefl0275 x u D R S_cls f E dv_R_f dv_R_u
                                      dv_R_x)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                                (nb095AlphaDummy248 x D R)),
                              ((nb095AlphaDummy245 D R S_cls E),
                                (nb095AlphaDummy246 x D R)),
                              ((nb095AlphaDummy004 D R S_cls E),
                                (nb095AlphaDummy006 x u D R S_cls f E)),
                              ((nb095AlphaDummy003 D R S_cls E),
                                (nb095AlphaDummy005 x u D R S_cls f E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)] D
                            (nb095FocusedRefl0006 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy253 D R S_cls E) from (by
          unfold nb095AlphaDummy253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy254 x) from (by
          unfold nb095AlphaDummy254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) from (by
          unfold nb095AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  1)))) (show x ≠ (nb095AlphaDummy252 x R) from (by
          unfold nb095AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy249 D R S_cls E) from (by
          unfold nb095AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy251 x R) from (by
          unfold nb095AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy247 D R S_cls E) from (by
          unfold nb095AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy248 x D R) from (by
          unfold nb095AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy245 D R S_cls E) from (by
          unfold nb095AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy246 x D R) from (by
          unfold nb095AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D
                    R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600 D
                    R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601 x
                    u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _)))))))))))))
                                (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0081 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0082 x u D R S_cls f E)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (nb095SplitAlpha0082 x u D R S_cls f E)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                    [((nb095AlphaDummy250 D R S_cls E),
                                        (nb095AlphaDummy252 x R)),
                                      ((nb095AlphaDummy249 D R S_cls E),
                                        (nb095AlphaDummy251 x R)),
                                      ((nb095AlphaDummy247 D R S_cls E),
                                        (nb095AlphaDummy248 x D R)),
                                      ((nb095AlphaDummy245 D R S_cls E),
                                        (nb095AlphaDummy246 x D R)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCcnv (synCdif R (synCid)))
                                    (nb095WppRefl0275 x u D R S_cls f E dv_R_f dv_R_u
                                      dv_R_x))))))))))))))) (TAlphaWff.conj
          (nb095SplitAlpha0101 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_E_f dv_E_u
            dv_E_x dv_R_f dv_R_u dv_R_x dv_S_f dv_S_u dv_S_x dv_f_u dv_f_x dv_u_x)
          (nb095SplitAlpha0102 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_E_f dv_E_u
            dv_E_x dv_R_f dv_R_u dv_R_x dv_S_f dv_S_u dv_S_x dv_f_u dv_f_x dv_u_x)))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_wecutiso`. -/
@[expose]
noncomputable def nominalDfWecutiso (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.classEq (synCwecutiso R D S_cls E) (.cab f (synWrex x D (synWrex u E
              (synWiso (.cv f) (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (.cv u))))
                    (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (.cv u))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (.cv u))))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb095AlphaDummy002 D R S_cls E), x),
                  ((nb095AlphaDummy000 D R S_cls E), f)]
                D (nb095FocusedRefl0000 x D R S_cls f E dv_D_f dv_D_x))) (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfReflOn [((nb095AlphaDummy001 D R S_cls E), u),
                      ((nb095AlphaDummy002 D R S_cls E), x),
                      ((nb095AlphaDummy000 D R S_cls E), f)]
                    E (nb095FocusedRefl0001 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                (TAlphaWff.conj (TAlphaWff.neg
                    (nb095SplitAlpha0078 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_E_f
                      dv_E_u dv_E_x dv_R_f dv_R_u dv_R_x dv_S_f dv_S_u dv_S_x dv_f_u
                      dv_f_x dv_u_x)) (TAlphaWff.all
                    (nb095SplitAlpha0103 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_E_f
                      dv_E_u dv_E_x dv_R_f dv_R_u dv_R_x dv_S_f dv_S_u dv_S_x dv_f_u
                      dv_f_x dv_u_x))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
