/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block043

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part119`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0096`. -/
@[expose]
noncomputable def nb090SplitAlpha0096 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (synWbr (Class.cv (nb090AlphaDummy041 A))
          (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
          (Class.cv (nb090AlphaDummy042 A))) (synWbr
          (synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy041 A)))
          (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
          (synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy042 A)))))
      (Wff.imp (synWbr (Class.cv (nb090AlphaDummy043 v u h))
          (synCfv (synC1st) (Class.cv u)) (Class.cv (nb090AlphaDummy044 v u h)))
        (synWbr (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
          (synCfv (synC1st) (Class.cv v))
          (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0084 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0085 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0085 v u A h))))))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq
                        (Class.cab (nb090AlphaDummy653 A)
                          (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                            (Class.cv (nb090AlphaDummy653 A))))
                        (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq
                        (Class.cab (nb090AlphaDummy654 u) (synWbr (Class.cv u) (synC1st)
                            (Class.cv (nb090AlphaDummy654 u))))
                        (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090SplitAlpha0086 v u A h dv_h_u dv_u_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy662 A) from (by
          unfold nb090AlphaDummy662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy664 u) from (by
          unfold nb090AlphaDummy664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy691 A) from (by
          unfold nb090AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy692 u) from (by
          unfold nb090AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy665 A) from (by
          unfold nb090AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy666 u) from (by
          unfold nb090AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)), ((nb090AlphaDummy662 A),
        (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)), ((nb090AlphaDummy665 A),
        (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)), ((nb090AlphaDummy658 A),
        (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy662 A) from (by
          unfold nb090AlphaDummy662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy664 u) from (by
          unfold nb090AlphaDummy664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy691 A) from (by
          unfold nb090AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy692 u) from (by
          unfold nb090AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy665 A) from (by
          unfold nb090AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy666 u) from (by
          unfold nb090AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)), ((nb090AlphaDummy662 A),
        (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)), ((nb090AlphaDummy665 A),
        (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)), ((nb090AlphaDummy658 A),
        (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                        [((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                          ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                          ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                          ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                          ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                          ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                          ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                          ((nb090AlphaDummy001 A), u),
                          ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                        (synC1st) (nb090WppRefl0298 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy655 A) ≠ (nb090AlphaDummy697 A) from (by
                              unfold nb090AlphaDummy697;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0726 A) 0))))
                          (show (nb090AlphaDummy656 u) ≠ (nb090AlphaDummy698 u) from (by
                              unfold nb090AlphaDummy698;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0727 u) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0090 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
        (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
        (Class.cv (nb090AlphaDummy777 A)))) (synCsn (Class.cv
        (nb090AlphaDummy779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
        (Class.cab (nb090AlphaDummy778 v u h) (synWbr (Class.cv
        (nb090AlphaDummy044 v u h)) (Class.cv h) (Class.cv (nb090AlphaDummy778 v u h))))
        (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777
        A) ≠ (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy777 A) from (by
          unfold nb090AlphaDummy777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090AlphaDummy778 v u h) from (by
          unfold nb090AlphaDummy778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy779 A) from (by
          unfold nb090AlphaDummy779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090AlphaDummy780 v u h) from (by
          unfold nb090AlphaDummy780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy782 A) from (by
          unfold nb090AlphaDummy782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy784 v u h) from (by
          unfold nb090AlphaDummy784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy781 A) from (by
          unfold nb090AlphaDummy781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy783 v u h) from (by
          unfold nb090AlphaDummy783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy700 A) from (by
          unfold
            nb090AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy702 v u h) from (by
          unfold
            nb090AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy699 A) from (by
          unfold
            nb090AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold
            nb090AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy775 A) from (by
          unfold
            nb090AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy776 v u h) from (by
          unfold
            nb090AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold
            nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy704 v u h) from (by
          unfold
            nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy042 A) from (by
          unfold
            nb090AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy044 v u h) from (by
          unfold
            nb090AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy041 A) from (by
          unfold
            nb090AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy043 v u h) from (by
          unfold
            nb090AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy779 A) ≠ (nb090AlphaDummy821 A) from (by
          unfold nb090AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090AlphaDummy780 v u h) ≠ (nb090AlphaDummy822 v u h) from
        (by
          unfold nb090AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (nb090SplitAlpha0093 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
        (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
        (Class.cv (nb090AlphaDummy777 A)))) (synCsn (Class.cv
        (nb090AlphaDummy779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
        (Class.cab (nb090AlphaDummy778 v u h) (synWbr (Class.cv
        (nb090AlphaDummy044 v u h)) (Class.cv h) (Class.cv (nb090AlphaDummy778 v u h))))
        (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777
        A) ≠ (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy777 A) from (by
          unfold nb090AlphaDummy777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090AlphaDummy778 v u h) from (by
          unfold nb090AlphaDummy778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy779 A) from (by
          unfold nb090AlphaDummy779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090AlphaDummy780 v u h) from (by
          unfold nb090AlphaDummy780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy782 A) from (by
          unfold nb090AlphaDummy782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy784 v u h) from (by
          unfold nb090AlphaDummy784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy781 A) from (by
          unfold nb090AlphaDummy781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy783 v u h) from (by
          unfold nb090AlphaDummy783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy700 A) from (by
          unfold
            nb090AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy702 v u h) from (by
          unfold
            nb090AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy699 A) from (by
          unfold
            nb090AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold
            nb090AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy775 A) from (by
          unfold
            nb090AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy776 v u h) from (by
          unfold
            nb090AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold
            nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy704 v u h) from (by
          unfold
            nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy042 A) from (by
          unfold
            nb090AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy044 v u h) from (by
          unfold
            nb090AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy041 A) from (by
          unfold
            nb090AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy043 v u h) from (by
          unfold
            nb090AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy779 A) ≠ (nb090AlphaDummy821 A) from (by
          unfold nb090AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090AlphaDummy780 v u h) ≠ (nb090AlphaDummy822 v u h) from
        (by
          unfold nb090AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))))))
                            (nb090SplitAlpha0093 v u A h)))))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq
                        (Class.cab (nb090AlphaDummy827 A)
                          (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                            (Class.cv (nb090AlphaDummy827 A))))
                        (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq
                        (Class.cab (nb090AlphaDummy828 v) (synWbr (Class.cv v) (synC1st)
                            (Class.cv (nb090AlphaDummy828 v))))
                        (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090SplitAlpha0094 v u A h dv_h_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy836 A) from (by
          unfold nb090AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy838 v) from (by
          unfold nb090AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy865 A) from (by
          unfold nb090AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy866 v) from (by
          unfold nb090AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy839 A) from (by
          unfold nb090AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy840 v) from (by
          unfold nb090AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)), ((nb090AlphaDummy836 A),
        (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)), ((nb090AlphaDummy839 A),
        (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)), ((nb090AlphaDummy832 A),
        (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy836 A) from (by
          unfold nb090AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy838 v) from (by
          unfold nb090AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy865 A) from (by
          unfold nb090AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy866 v) from (by
          unfold nb090AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy839 A) from (by
          unfold nb090AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy840 v) from (by
          unfold nb090AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)), ((nb090AlphaDummy836 A),
        (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)), ((nb090AlphaDummy839 A),
        (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)), ((nb090AlphaDummy832 A),
        (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                        [((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                          ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                          ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                          ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                          ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                          ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                          ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                          ((nb090AlphaDummy001 A), u),
                          ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                        (synC1st) (nb090WppRefl0327 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy829 A) ≠ (nb090AlphaDummy871 A) from (by
                              unfold nb090AlphaDummy871;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0926 A) 0))))
                          (show (nb090AlphaDummy830 v) ≠ (nb090AlphaDummy872 v) from (by
                              unfold nb090AlphaDummy872;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0927 v) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part120`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0097`. -/
@[expose]
noncomputable def nb090SplitAlpha0097 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (synWbr (synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))
          (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
          (synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy042 A))))
        (synWbr (Class.cv (nb090AlphaDummy041 A))
          (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
          (Class.cv (nb090AlphaDummy042 A))))
      (Wff.imp (synWbr (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
          (synCfv (synC1st) (Class.cv v))
          (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h))))
        (synWbr (Class.cv (nb090AlphaDummy043 v u h))
          (synCfv (synC1st) (Class.cv u)) (Class.cv (nb090AlphaDummy044 v u h)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0090 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
        (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
        (Class.cv (nb090AlphaDummy777 A)))) (synCsn (Class.cv
        (nb090AlphaDummy779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
        (Class.cab (nb090AlphaDummy778 v u h) (synWbr (Class.cv
        (nb090AlphaDummy044 v u h)) (Class.cv h) (Class.cv (nb090AlphaDummy778 v u h))))
        (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777
        A) ≠ (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy777 A) from (by
          unfold nb090AlphaDummy777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090AlphaDummy778 v u h) from (by
          unfold nb090AlphaDummy778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy779 A) from (by
          unfold nb090AlphaDummy779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090AlphaDummy780 v u h) from (by
          unfold nb090AlphaDummy780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy782 A) from (by
          unfold nb090AlphaDummy782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy784 v u h) from (by
          unfold nb090AlphaDummy784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy781 A) from (by
          unfold nb090AlphaDummy781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy783 v u h) from (by
          unfold nb090AlphaDummy783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy700 A) from (by
          unfold
            nb090AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy702 v u h) from (by
          unfold
            nb090AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy699 A) from (by
          unfold
            nb090AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold
            nb090AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy775 A) from (by
          unfold
            nb090AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy776 v u h) from (by
          unfold
            nb090AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold
            nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy704 v u h) from (by
          unfold
            nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy042 A) from (by
          unfold
            nb090AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy044 v u h) from (by
          unfold
            nb090AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy041 A) from (by
          unfold
            nb090AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy043 v u h) from (by
          unfold
            nb090AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy779 A) ≠ (nb090AlphaDummy821 A) from (by
          unfold nb090AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090AlphaDummy780 v u h) ≠ (nb090AlphaDummy822 v u h) from
        (by
          unfold nb090AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (nb090SplitAlpha0093 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
        (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
        (Class.cv (nb090AlphaDummy777 A)))) (synCsn (Class.cv
        (nb090AlphaDummy779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
        (Class.cab (nb090AlphaDummy778 v u h) (synWbr (Class.cv
        (nb090AlphaDummy044 v u h)) (Class.cv h) (Class.cv (nb090AlphaDummy778 v u h))))
        (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy777
        A) ≠ (nb090AlphaDummy786 A) from (by
          unfold
            nb090AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from
        (by
          unfold
            nb090AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy785 A) from (by
          unfold
            nb090AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from
        (by
          unfold
            nb090AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy815 A) from (by
          unfold
            nb090AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy816 v u h) from
        (by
          unfold
            nb090AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy777 A) ≠
        (nb090AlphaDummy789 A) from (by
          unfold
            nb090AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy790 v u h) from
        (by
          unfold
            nb090AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy044 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u
        h)), ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789
        A), (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A), (nb090AlphaDummy778
        v u h)), ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u
        h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775
        A), (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A), (nb090AlphaDummy704
        v u h)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A),
        h), ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy777 A) from (by
          unfold nb090AlphaDummy777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090AlphaDummy778 v u h) from (by
          unfold nb090AlphaDummy778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy779 A) from (by
          unfold nb090AlphaDummy779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090AlphaDummy780 v u h) from (by
          unfold nb090AlphaDummy780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy782 A) from (by
          unfold nb090AlphaDummy782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy784 v u h) from (by
          unfold nb090AlphaDummy784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy781 A) from (by
          unfold nb090AlphaDummy781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy783 v u h) from (by
          unfold nb090AlphaDummy783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy700 A) from (by
          unfold
            nb090AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy702 v u h) from (by
          unfold
            nb090AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy699 A) from (by
          unfold
            nb090AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold
            nb090AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy775 A) from (by
          unfold
            nb090AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy776 v u h) from (by
          unfold
            nb090AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold
            nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy704 v u h) from (by
          unfold
            nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy042 A) from (by
          unfold
            nb090AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090AlphaDummy044 v u h) from (by
          unfold
            nb090AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy041 A) from (by
          unfold
            nb090AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy043 v u h) from (by
          unfold
            nb090AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy779 A) ≠ (nb090AlphaDummy821 A) from (by
          unfold nb090AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090AlphaDummy780 v u h) ≠ (nb090AlphaDummy822 v u h) from
        (by
          unfold nb090AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))))))
                            (nb090SplitAlpha0093 v u A h)))))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq
                        (Class.cab (nb090AlphaDummy827 A)
                          (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                            (Class.cv (nb090AlphaDummy827 A))))
                        (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq
                        (Class.cab (nb090AlphaDummy828 v) (synWbr (Class.cv v) (synC1st)
                            (Class.cv (nb090AlphaDummy828 v))))
                        (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090SplitAlpha0094 v u A h dv_h_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy836 A) from (by
          unfold nb090AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy838 v) from (by
          unfold nb090AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy865 A) from (by
          unfold nb090AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy866 v) from (by
          unfold nb090AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy839 A) from (by
          unfold nb090AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy840 v) from (by
          unfold nb090AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)), ((nb090AlphaDummy836 A),
        (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)), ((nb090AlphaDummy839 A),
        (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)), ((nb090AlphaDummy832 A),
        (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy836 A) from (by
          unfold nb090AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy838 v) from (by
          unfold nb090AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy865 A) from (by
          unfold nb090AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy866 v) from (by
          unfold nb090AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy827 A) ≠
        (nb090AlphaDummy839 A) from (by
          unfold nb090AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy840 v) from (by
          unfold nb090AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)), ((nb090AlphaDummy836 A),
        (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)), ((nb090AlphaDummy839 A),
        (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)), ((nb090AlphaDummy832 A),
        (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                        [((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                          ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                          ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                          ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                          ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                          ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                          ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                          ((nb090AlphaDummy001 A), u),
                          ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                        (synC1st) (nb090WppRefl0327 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy829 A) ≠ (nb090AlphaDummy871 A) from (by
                              unfold nb090AlphaDummy871;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0926 A) 0))))
                          (show (nb090AlphaDummy830 v) ≠ (nb090AlphaDummy872 v) from (by
                              unfold nb090AlphaDummy872;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0927 v) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0084 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0085 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090SplitAlpha0085 v u A h))))))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq
                        (Class.cab (nb090AlphaDummy653 A)
                          (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                            (Class.cv (nb090AlphaDummy653 A))))
                        (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq
                        (Class.cab (nb090AlphaDummy654 u) (synWbr (Class.cv u) (synC1st)
                            (Class.cv (nb090AlphaDummy654 u))))
                        (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090SplitAlpha0086 v u A h dv_h_u dv_u_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy662 A) from (by
          unfold nb090AlphaDummy662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy664 u) from (by
          unfold nb090AlphaDummy664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy691 A) from (by
          unfold nb090AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy692 u) from (by
          unfold nb090AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy665 A) from (by
          unfold nb090AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy666 u) from (by
          unfold nb090AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)), ((nb090AlphaDummy662 A),
        (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)), ((nb090AlphaDummy665 A),
        (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)), ((nb090AlphaDummy658 A),
        (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy662 A) from (by
          unfold nb090AlphaDummy662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy664 u) from (by
          unfold nb090AlphaDummy664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy691 A) from (by
          unfold nb090AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy692 u) from (by
          unfold nb090AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy653 A) ≠
        (nb090AlphaDummy665 A) from (by
          unfold nb090AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy666 u) from (by
          unfold nb090AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)), ((nb090AlphaDummy662 A),
        (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)), ((nb090AlphaDummy665 A),
        (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)), ((nb090AlphaDummy658 A),
        (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                        [((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                          ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                          ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                          ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                          ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                          ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                          ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                          ((nb090AlphaDummy001 A), u),
                          ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                        (synC1st) (nb090WppRefl0298 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy655 A) ≠ (nb090AlphaDummy697 A) from (by
                              unfold nb090AlphaDummy697;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0726 A) 0))))
                          (show (nb090AlphaDummy656 u) ≠ (nb090AlphaDummy698 u) from (by
                              unfold nb090AlphaDummy698;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0727 u) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
